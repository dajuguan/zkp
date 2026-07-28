# Understanding Stark and FRI
## KZG vs FRI: 为什么KZG不需要low degree testing
**KZG:** 一开始就是polynomial commitment, 并且即使想通过高阶多项式伪造f(x)，最多也就是伪造成SRS的次数n(一般2^32)，被抓住的概率还是很大( 1- 2^32/2^256)
```
Polynomial
    │
Commit
    │
Random Opening
    │
Schwartz-Zippel
```

**FRI:** 一开始只是vector commitment，需要通过FRI把vector lift为polynomial(或者说合法的RS Code)，否则他在merkle proof eval的点x就没有意义
- x 本来的含义是f(x)在x点的值，但是vector的话，就是第x个元素的值，就很随意；不是多项式就没法用Schwartz-Zippel证明了

```
Vector
    │
Commit(Merkle)
    │
Low Degree Test
    │
现在才能视作 Polynomial(合法的RS Code)
    │
Random Opening
    │
Schwartz-Zippel
```

## How to run: 
```
Require: python^3.11.5, Optional: pip install tqdm
python main.py
```

## Ref:
- [stark101 code **with verifier**](https://github.com/udibr/stark101-1/blob/master/tutorial/Stark101-part5.ipynb)
- [Vitalik: STARKs, Part I: Proofs with Polynomials](https://vitalik.eth.limo/general/2017/11/09/starks_part_1.html)
- [Vitalik: STARKs, Part II: Thank Goodness It's FRI-day](https://vitalik.eth.limo/general/2017/11/22/starks_part_2.html)
- [Vitalik: STARKs, Part 3: Into the Weeds](https://vitalik.eth.limo/general/2018/07/21/starks_part_3.html)
- [Paper: Scalable, transparent, and post-quantum secure computational integrity](https://eprint.iacr.org/2018/046.pdf)
- [Paper: A summary on the FRI low degree test](https://eprint.iacr.org/2022/1216.pdf)
- [Paper: ZERO KNOWLEDGE VIRTUAL MACHINE STEP BY STEP](https://eprint.iacr.org/2023/1032.pdf)
- [Anatomy of a STARK](https://aszepieniec.github.io/stark-anatomy/)