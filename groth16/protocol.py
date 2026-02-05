"""
A = u(x)
B = v(x)
C = w(x) + h(x)t(x)

=>
[A]_1 · [B]_2 = [C]_1 · G_2
"""

# Expand QAP
# force the prover to use the correct polynomial without forging the proof.
"""
by introducing two random scalas that prover don't know: α and β

(α + A)(β + B) = αβ + αA + βB + AB = αβ + (αA + βB + w(x) + h(x)t(x))
let A = α + A, B = β + B, C = αA + βB + w(x) + h(x)t(x), 
then prover had to prove the following equation:
[A]_1 · [B]_2 = [α]_1 · [β]_2 +  [C]_1 · G_2

为什么必须两个随机数？保证A和B在setup中被commit，如果只对A加随机数，那么setup和B没关系，导致可以修改B来构造witness。
"""

# Introducing γ and/or δ from misusing public inputs
"""
For setup: 
X = (public inputs commitment)/γ
C = (private inputs commitment)/δ
other components needs to divide by γ and/or δ accordingly.
(α + A)(β + B) = αβ + C_pub * γ + C_priate * δ

Prover side doesn't change.
Verify:
[A]_1 · [B]_2 = [α]_1 · [β]_2 +  [X]_1 · [γ]_2  + [C]_1 · [δ]_2
"""


# Prover enforce true zero knowledge: r and s, to avoid guessing witness by recontruct proof
"""
for private inputs:
(α + A + rδ)(β + B + sδ) = αβ + C + δ()
"""

# Malleability（可塑性=>延展性)
"""
操作可通过验证的[A]_1,[B]_2 proof，来对相同的witness，构造不同的proof，比如-A, -B；或者左右两边添加一对随机的delta。
解决办法: 在public inputs上绑定一些witness作为nullifier，一旦这个public inputs被用过那么即使proof验证通过也不行；
- 签名不行：无法防御proof对相同witness生成的不同proof变体签名

"""
