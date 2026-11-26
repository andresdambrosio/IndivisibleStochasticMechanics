# Contributing

This is an **AI-first** formalization project. We want AI tools to do as much of the heavy
lifting as possible, at any scale. We keep the project credible by concentrating human
trust in one thin, explicit layer.

Contributions come in three kinds, and all three are welcome: **Lean proofs**, **book
chapters** (in English and Spanish, see `book/en/` and `book/es/`), and **human review** of the trusted layer.

## The model: free proofs, trusted definitions

Lean checks that a proof proves what is written. It cannot check that what is written is
what the physics means. So we split the project in two:

| | Who may write it | What guarantees it |
|---|---|---|
| **Proofs** (any `theorem`/`lemma` body) | anyone, including AI, at any scale | Lean. If it compiles, it is correct. No human line-by-line review needed. |
| **Trusted layer**: every definition, plus the *statements* of main theorems | anyone, including AI | a human who checked it against the source, recorded in [TRUSTED.md](TRUSTED.md) |
| **References** | anyone | a human who checked the actual paper, recorded in [TRUSTED.md](TRUSTED.md) |

The trusted layer is small, around one definition for every few theorems. That is the only
bottleneck, and it is what lets everything else scale.

## The trusted layer

- **Every new `def` or `structure` must be added to [TRUSTED.md](TRUSTED.md)**, with what
  it is meant to capture, its source, and any interpretive choice. CI fails otherwise
  (`scripts/check_trusted.py`).
- New entries start as ⏳ *pending*. AI may write them, and they can be merged while pending.
- A human reviewer changes the status to ✅ with their name and date after checking that
  the Lean statement matches the cited source.
- **Changing a ✅ definition resets it to ⏳**, and the pull request must say so explicitly.
- Before an external claim (a paper, a talk, an announcement), every declaration that the
  claim depends on must be ✅.

## Where to start

- Issues labelled [`good first issue`](https://github.com/andresdambrosio/IndivisibleStochasticMechanics/labels/good%20first%20issue)
  are small, self-contained, and explained in the book.
- Reviewing a ⏳ entry in [TRUSTED.md](TRUSTED.md) is a high-value contribution that
  needs physics, not Lean.
- [ROADMAP.md](ROADMAP.md) lists everything planned. Open or comment on an issue before
  starting something big.

## Setup

```bash
# install elan once: https://lean-lang.org/install
git clone https://github.com/andresdambrosio/IndivisibleStochasticMechanics
cd IndivisibleStochasticMechanics
lake exe cache get
lake build --wfail
python3 scripts/check_trusted.py
```

## Rules for Lean code

1. **`main` builds with no warnings and no `sorry`.** CI runs `lake build --wfail`.
2. **Reuse Mathlib.** Search Mathlib before defining something new.
3. **Cite the source** in the docstring of every definition and main theorem.
4. **Follow Mathlib style.** Use its naming conventions, a module docstring at the top of
   each file, and lines of at most 100 characters.
5. **Put everything in the `ISM` namespace.** Files start with `module` and use
   `@[expose] public section`.

## Rules for the book

- The book exists in English (`book/en/`, the default, published at the site root) and
  Spanish (`book/es/`, published under `es/`). Both use the same file names, and every
  change goes into both.
- **Credit every idea.** Each result that comes from someone else is attributed to its
  author, with a citation and a link, in the paragraph where it appears, and listed in
  `99-references.md`. Only what is genuinely original to the project is presented as
  ours, and then it says so explicitly.
- Every chapter describes verified code, or is clearly marked 🚧.
- Structure: physical idea → mathematics → Lean → exercises.
- If you change a declaration, update the chapter that quotes it.
- Licence: book CC BY 4.0 (`book/LICENSE`); the book's author is Andrés D'Ambrosio, code Apache 2.0 (`LICENSE`).

## Pull requests

- Say which tools you used. This is information, not a judgement: AI-written proofs are
  welcome.
- One topic per pull request. Reference the issue it closes.
- CI must be green: Lean build plus the trusted-layer check.

## Contributing upstream

When we upstream results to [physlib](https://github.com/leanprover-community/physlib) or
Mathlib, **their** policies apply. Physlib, for example, requires a human to vouch for
every line and to communicate with reviewers personally. Read their `AI-POLICY.md` first.
