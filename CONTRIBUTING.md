# Contributing

Thanks for your interest! Contributions come in three kinds, and all three are welcome:
**Lean proofs**, **book chapters** (in Spanish, see `book/`), and **physics review** of
definitions and claims.

## Where to start

- Issues labelled [`good first issue`](https://github.com/andresdambrosio/IndivisibleStochasticMechanics/labels/good%20first%20issue)
  are small, self-contained, and explained in the book.
- [ROADMAP.md](ROADMAP.md) lists everything planned. Comment on an issue, or open one,
  before starting something big, so that two people don't do the same work.
- Questions are welcome in the issues and on the [Lean Zulip](https://leanprover.zulipchat.com).

## Setup

```bash
# install elan once: https://lean-lang.org/install
git clone https://github.com/andresdambrosio/IndivisibleStochasticMechanics
cd IndivisibleStochasticMechanics
lake exe cache get
lake build
```

## Rules for Lean code

1. **`main` builds with no warnings and no `sorry`.** CI runs `lake build --wfail`.
   Run it locally before opening a pull request.
2. **Reuse Mathlib.** Search Mathlib before defining something new. For example, we use
   `Matrix.colStochastic` rather than our own definition of stochastic matrices.
3. **Cite the source.** Every definition and main theorem says in its docstring which
   paper and section it formalizes, e.g. `arXiv:2302.10778, §3`.
4. **Follow Mathlib style.** Naming conventions, a module docstring (`/-! ... -/`) at the
   top of each file, and lines of at most 100 characters.
5. **Put everything in the `ISM` namespace.** Files start with `module` and expose their
   API with `@[expose] public section`.

## Rules for the book

- Every chapter describes code that is already verified, or is clearly marked 🚧.
- Each chapter has the same structure: physical idea → mathematics → Lean → exercises.
- If you change a declaration, update the chapter that quotes it.
- The book is licensed CC BY 4.0 (`book/LICENSE`). Code is Apache 2.0 (`LICENSE`).

## Use of AI tools

AI assistants are allowed, and this project was started with the help of one (Claude).
If you use them:

- **Say so in your pull request** and indicate roughly what was AI-assisted.
- **You are responsible for what you submit.** Lean checks the proofs, but it does not
  check that a definition means what the docstring says, or that the book's physics is
  right. Read and understand everything you submit.

## Pull requests

- One topic per pull request, with a clear title. Reference the issue it closes.
- CI must be green before review.
