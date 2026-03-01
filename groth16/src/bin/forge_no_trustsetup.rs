use std::env;
use std::fs;
use std::str::FromStr;

use anyhow::{Result, anyhow};
use ark_bn254::{Fq, Fr, G1Affine};
use ark_ec::{AffineRepr, CurveGroup, Group};
use ark_ff::PrimeField;
use serde_json::{Value, json};

fn parse_g1(coords: &[Value]) -> Result<G1Affine> {
    if coords.len() < 2 {
        return Err(anyhow!("invalid G1 point: expected at least [x, y]"));
    }

    let x = coords[0]
        .as_str()
        .ok_or_else(|| anyhow!("invalid G1 x coordinate: expected decimal string"))?;
    let y = coords[1]
        .as_str()
        .ok_or_else(|| anyhow!("invalid G1 y coordinate: expected decimal string"))?;

    let x = Fq::from_str(x).map_err(|_| anyhow!("invalid G1 x field element"))?;
    let y = Fq::from_str(y).map_err(|_| anyhow!("invalid G1 y field element"))?;

    let p = G1Affine::new_unchecked(x, y);
    if !p.is_on_curve() {
        return Err(anyhow!("invalid G1 point: not on curve"));
    }
    Ok(p)
}

fn point_to_vk_json(point: G1Affine) -> Value {
    json!([
        point.x.into_bigint().to_string(),
        point.y.into_bigint().to_string(),
        "1"
    ])
}

// forge a proof for c = a * b, where c = target_c without knowing a, b
fn main() -> Result<()> {
    let target_c = env::args()
        .nth(1)
        .map(|s| s.parse::<u64>())
        .transpose()?
        .unwrap_or(999);

    let vk_raw = fs::read_to_string("./outputs/multi/vkey.json")?;
    let vk: Value = serde_json::from_str(&vk_raw)?;

    let alpha_coords = vk["vk_alpha_1"]
        .as_array()
        .ok_or_else(|| anyhow!("missing vk_alpha_1 array"))?;
    let ic = vk["IC"]
        .as_array()
        .ok_or_else(|| anyhow!("missing IC array"))?;
    if ic.len() < 2 {
        return Err(anyhow!("IC must contain at least IC[0], IC[1]"));
    }

    let ic0_coords = ic[0].as_array().ok_or_else(|| anyhow!("invalid IC[0]"))?;
    let ic1_coords = ic[1].as_array().ok_or_else(|| anyhow!("invalid IC[1]"))?;

    let alpha = parse_g1(alpha_coords)?;
    let ic0 = parse_g1(ic0_coords)?;
    let ic1 = parse_g1(ic1_coords)?;

    let c_scalar = Fr::from(target_c);
    let vk_x =
        (ic0.into_group() + ic1.into_group().mul_bigint(c_scalar.into_bigint())).into_affine();
    let c_point = (-vk_x.into_group()).into_affine();

    let proof = json!({
        "pi_a": point_to_vk_json(alpha),
        "pi_b": vk["vk_beta_2"].clone(),
        "pi_c": point_to_vk_json(c_point),
        "protocol": "groth16",
        "curve": "bn128"
    });
    let public = json!([target_c.to_string()]);

    fs::write(
        "./outputs/forged_proof.json",
        serde_json::to_string_pretty(&proof)?,
    )?;
    fs::write(
        "./outputs/forged_public.json",
        serde_json::to_string_pretty(&public)?,
    )?;

    println!("Forged proof for c = {target_c}");
    println!("  A = alpha from VK");
    println!("  B = beta from VK");
    println!(
        "  C = -vk_x = (vk_x.x, bn254_prime_field - vk_x.y) = \n ({}, {})",
        c_point.x.into_bigint(),
        c_point.y.into_bigint()
    );
    println!("Written: ./outputs/forged_proof.json, ./outputs/forged_public.json");

    Ok(())
}
