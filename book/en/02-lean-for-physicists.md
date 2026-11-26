# 2. Lean for physicists, the bare minimum

This chapter is not a Lean course. Its goal is for you to be able to **read** the
project's code and change it a little. To go deeper, the best resource is
[*Mathematics in Lean*](https://leanprover-community.github.io/mathematics_in_lean/), by
Jeremy Avigad and Patrick Massot.

## Three ideas

**1. Everything has a type.** `ℝ` is the type of real numbers, `ℂ` that of complex
numbers, and `Matrix n n ℝ` that of real matrices with rows and columns indexed by `n`. A
"finite configuration space" is simply a type `n` with the property `[Fintype n]`: it has
finitely many elements.

**2. Propositions are types too, and proofs are their elements.** Writing

```lean
theorem foo : 2 + 2 = 4 := by norm_num
```

means "`foo` is a proof of `2 + 2 = 4`, built with the tactic `norm_num`". If Lean accepts
the file, the proof is correct.

**3. Tactics are the steps of the proof.** After `by` you write a sequence of steps. The
most common ones in this project are:

| Tactic | What it does |
|---|---|
| `simp [lemmas]` | simplifies using rewrite rules |
| `rw [h]` | rewrites using the equality `h` |
| `linarith` | closes goals that are linear inequalities or equalities |
| `positivity` | proves that something is $\geq 0$ or $> 0$ |
| `ext i j` | to prove two matrices equal, proves they agree entry by entry |
| `fin_cases i` | splits into cases over the possible values of `i : Fin 2` |
| `exact h` | "this is exactly `h`" |

## How to read a definition

```lean
structure IsProbDist (p : n → ℝ) : Prop where
  nonneg : ∀ i, 0 ≤ p i
  sum_eq_one : ∑ i, p i = 1
```

In words: "A function $p$ from configurations to the reals *is a probability
distribution* if it satisfies two things: $p_i \geq 0$ for every $i$, and
$\sum_i p_i = 1$". A `structure` of type `Prop` bundles several conditions into one.

## Mathlib

[Mathlib](https://github.com/leanprover-community/mathlib4) is Lean's large library of
mathematics, written by hundreds of contributors
([The mathlib Community, 2020](https://arxiv.org/abs/1910.09336)). We do not reinvent
anything it already has: matrices, complex numbers, unitary groups, trigonometry, measure
theory. For example, we use its definition of a column-stochastic matrix
(`Matrix.colStochastic`), and so we inherit all its theorems.

## Structure of a project file

```lean
module                          -- uses Lean's module system
public import Mathlib           -- which other files it needs

/-! # Title
Explanation in prose, references to the papers. -/

@[expose] public section        -- what follows is visible to anyone importing the file

namespace ISM                   -- all our definitions live in `ISM.`
...
end ISM
```

## `sorry`

`sorry` is a "blank" proof: Lean accepts it, but flags the file with a warning. It is
useful for writing the statements first and proving them later. In this project, the
`main` branch must not contain any `sorry`.

## Exercises

1. Install Lean ([lean-lang.org/install](https://lean-lang.org/install)), clone the
   repository and run `lake build`.
2. Open `IndivisibleStochasticMechanics/Stochastic/Basic.lean` in VS Code with the Lean
   extension. Put the cursor inside a proof and look at the *Lean Infoview* panel: it
   shows the goal that remains to be proved at each step.
