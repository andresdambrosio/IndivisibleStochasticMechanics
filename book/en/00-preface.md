# 0. Preface

## What this book is

It is the logbook of a project with two goals:

1. Take the reformulation of quantum mechanics proposed by **Jacob A. Barandes**
   (Harvard) in [Barandes, 2023a](https://arxiv.org/abs/2302.10778),
   [Barandes, 2023b](https://arxiv.org/abs/2309.03085) and
   [Barandes, 2025](https://arxiv.org/abs/2507.21192), in which quantum systems are
   *indivisible stochastic processes*, and **verify each of its theorems with a proof
   assistant**: Lean 4.
2. From there, **extend it** so that it covers everything textbook quantum mechanics
   does, and find out whether at some point it says something new.

The inspiration comes from what is happening in mathematics. With
[Lean 4](https://lean-lang.org/) ([de Moura and Ullrich, 2021](https://doi.org/10.1007/978-3-030-79876-5_37))
and its library **Mathlib** ([The mathlib Community, 2020](https://arxiv.org/abs/1910.09336)),
thousands of people formalize mathematics collaboratively: a computer checks every
theorem, and nobody has to "trust" a proof. We want the same for one concrete program in
the foundations of physics.

## Authorship

The book and the formalization are by **Andrés D'Ambrosio**. The theory being formalized
is Jacob Barandes', and the classic results we use belong to their respective authors.
Each chapter says whose idea each result is, with the citation and the link. When
something is an original contribution of the project (a formal proof, a construction or a
new example), we say so explicitly. The full list of sources is in the
[references](99-references.md).

## Who it is for

Physics or mathematics students who have seen linear algebra and a first course in
quantum mechanics. You do not need to know Lean: chapter 2 explains what is needed, and
each chapter walks through the code line by line.

## How to read it

Every chapter has the same structure:

- **The physical idea**: what we want to capture and why it matters.
- **The mathematics**: definitions and theorems, with proofs on paper.
- **In Lean**: how it was written in the repository and what each part does.
- **Exercises**: some with pencil and paper, some in Lean. Several Lean exercises are real
  open tasks of the project.

## How to follow along with the code

```bash
git clone https://github.com/andresdambrosio/IndivisibleStochasticMechanics
cd IndivisibleStochasticMechanics
lake exe cache get
lake build
```

If `lake build` finishes without errors, every proof in the book marked as verified really
is verified, on your own machine.

## How we work: AI and the trusted layer

This project is done with heavy use of artificial intelligence, and we do not hide it: it
is part of the experiment. The obvious question is why you should trust something largely
written by an AI. The answer has two parts.

**Proofs need no trust.** Lean checks every step. If the file compiles, the proof is
correct, no matter who or what wrote it. That is why the AI can write proofs freely.

**Definitions do need trust.** Lean checks that we proved *what we wrote*, not that what
we wrote is *what the physics means*. If we define "division event" wrongly, every
theorem about division events is perfectly verified and perfectly irrelevant. No computer
can detect that error, because it is an error of *meaning*.

That is why the project has a **trusted layer**: the file `TRUSTED.md` lists every
definition and every main statement, what it is meant to capture, which paper it comes
from, and whether a person has reviewed it (✅) or not yet (⏳). CI prevents adding a new
definition without registering it there. All human trust is concentrated in that layer,
which is small, and everything else can grow as much as needed.

Throughout the book, when we present a definition, we discuss the **interpretive
choices** we made when formalizing it. Those discussions are physics, not programming,
and they are the most important part of the course.

## About the name

Barandes speaks of *indivisible stochastic processes* and of the *stochastic-quantum
correspondence*. In this course we use **Indivisible Stochastic Mechanics** (ISM) as a
short name for the whole. It is our label, not a theory different from Barandes'. Do not
confuse it with Edward Nelson's *stochastic mechanics*
([Nelson, 1966](https://doi.org/10.1103/PhysRev.150.1079)), which is a different theory
based on Markovian diffusion processes.
