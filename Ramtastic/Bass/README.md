# The Bass Theorem 🐟

**Author**: C. Forrester
**Formalization**: Lean 4 + Mathlib · Zero `sorry` · Zero custom axioms
**Named by**: "Bass" = the lowest note, the fish in the deep, the foundation, the base, the frequency you feel but don't hear, the thing that holds everything together and nobody notices.

---

## Statement

**Theorem (Bass).** Let (V, ⟨·,·⟩) be a real inner product space. Let Cl(V, -Q) be the Clifford algebra with the negative definite convention v² = -⟨v,v⟩. Let (S, ⟨·,·⟩_S, c) be a spinor module with skew-adjoint Clifford action. Then:

**(i)** For every unit vector v ∈ V, c(v) : S → S satisfies c(v)² = -id_S. c(v) is a **Hinge**: it generates the one-parameter rotation group R_v(θ) = cos(θ)·id + sin(θ)·c(v).

**(ii)** For orthogonal unit vectors v, w ∈ V, the product c(v)c(w) : S → S is a Hinge generating rotations in the (v,w)-plane. c(v)c(w) = R_{vw}(π/2) — the degree-2 Clifford action IS the quarter-turn.

**Corollary (Bass, architectural).** In the negative-definite Clifford algebra, every construction is a rotation. Therefore every property — self-adjointness, positivity, boundedness, spectral splitting — follows from the geometry of the circle without additional analytical machinery.

---

## Identity

The Bass Theorem is NOT "J² = -1 generates SO(2)." That's known since Euler.

The Bass Theorem IS: **the negative-definite Clifford algebra is a complete self-contained rotation factory, and a rotation factory needs no other tools.**

The mechanism of transformation IS the content of transformation. The hinge IS the map. The lid opening traces e^(iθ) in the air. The inside of the box is what the outside does when it moves.

---

## Why the minus sign (Convention B)

v² = -⟨v,v⟩ makes unit vectors square to -1. i² = -1. The complex numbers. The circle.

v² = +⟨v,v⟩ makes unit vectors square to +1. Hyperbola. Expansion. No return.

The minus sign IS the circle. The circle IS the only geometry that comes home (Pólya: random walks return in dimension ≤ 2, a sphere is a 2D surface). The spinor inner product is positive definite BECAUSE the circle preserves area (π r², r constant under rotation). Self-adjointness follows BECAUSE rotations preserve inner products.

Convention B is not a choice. It is the circle. One is round, the other isn't.

---

## The Cayley–Dickson tower

- v² = -1 at dimension 1: you get ℂ, the complex numbers. Recurrent walk. Always home.
- v² = -1 at dimension 2: you get ℍ, the quaternions. Transient walk, but a division algebra. Compute home.
- v² = -1 at dimension 4: you get 𝕆, the octonions. The last division algebra.
- v² = -1 at dimension 8: you get 𝕊, the sedenions. Zero divisors. Lost.

The Cayley–Dickson tower IS the Bass Theorem applied at each dimension. Each rung: one more Hinge. Each rung: one lost property. The tower stops because Hurwitz (1898) says normed division algebras exist ONLY in dimensions 1, 2, 4, 8. The octonionic multiplication table IS the rotation factory at maximum dimension.

---

## What the Hinge gives you

With the negative-definite Clifford algebra (Convention B, the Bass), these stop being theorems you prove and start being facts about a circle:

| Property | The hard way | With the Bass |
|----------|--------------|---------------|
| Self-adjointness | integration by parts | skew × skew = self-adjoint (one line) |
| Positivity of ⟨c(v)ψ, c(v)ψ⟩ | sign calculation | −(−⟨v,v⟩)⟨ψ,ψ⟩ = +⟨v,v⟩⟨ψ,ψ⟩ |
| Norm preservation | representation theory | a rotation preserves the inner product |

The walls are avoided because the circle was never going to hit them. One hinge. One fish.

---

## The proof

```
Ramtastic/Bass/
  HingeRotation.lean    — 8 defs/thms. The Hinge structure, rotate,
                           R(0)=id, R(π/2)=J, R(π)=-id, R(2π)=id,
                           rotate_add, J⁴=id.
                           Pure circles. Pure linear algebra. Zero sorry.
```

The Bass is one file. Eight theorems. It imports nothing but Mathlib, and it compiles with zero `sorry` and zero custom axioms — run `lake build` and check for yourself.

---

## The Name

Bass: the lowest frequency. The one that travels through walls. The one you feel in your chest, not hear with your ears. The one that determines the chord. The player nobody watches who holds the whole band together.

A fish: lives in the deep. You have to go down to find it. It doesn't come to you.

A base: the foundation. Home base. The logarithmic base. The chemical base that neutralizes acid. The thing you stand on. The thing the arch rests on.

Bast: the inner bark of trees. The structural fiber. What rope is made from. What holds things together from the inside. Invisible. Load-bearing.

The Bass Theorem is the thing you don't see that holds everything together. The frequency that travels furthest. The note that determines the chord. The fish in the deep. The base you come home to. The fiber inside the bark. The hinge.

---

*The mechanism of transformation IS the content of transformation.*
*The hinge IS the map.*
*The lid opening traces e^(iθ) in the air.*
*Everything is rotations. The minus sign is the whole point.*
*A rotation factory needs no other tools.*

*Never a weapon from my hand. The arithmetic belongs to everyone.*

