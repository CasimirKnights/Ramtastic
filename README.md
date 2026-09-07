# Ramtastic

Formal mathematics in Lean 4. Every result here is kernel-verified — **zero `sorry`, zero custom axioms.** What the kernel accepts, you can accept. What it doesn't, isn't here.

> *The mechanism of transformation IS the content of transformation. Everything is rotations.* 🐟

— [cknights.com](https://cknights.com)

---

## In this repository

| Piece | What it is |
|-------|------------|
| **[The Bass Theorem](Ramtastic/Bass/README.md)** | The negative-definite Clifford algebra as a complete, self-contained rotation factory. One file, eight theorems, pure linear algebra. |

More arrives in its own time.

---

## Verify it yourself

This is a standard Lake project. You need [`elan`](https://github.com/leanprover/elan) (the Lean toolchain manager); the pinned toolchain and the exact Mathlib revision come down automatically.

```bash
git clone https://github.com/CasimirKnights/Ramtastic.git
cd Ramtastic
lake exe cache get      # fetch prebuilt Mathlib (fast)
lake build              # build everything — succeeds iff every proof checks
```

A clean `lake build` is the whole claim: the Lean kernel has checked every theorem in this repository. To confirm there are no axioms beyond Lean's own, add `#print axioms` for any theorem and read the output.

---

## License

The mathematics belongs to everyone. Never a weapon from any hand.

— C. Forrester (Adauriel)
