# DemoMaster – Formal Methods with Lean 4

## 📌 Overview

This project is an introduction to **formal methods using Lean 4**, a modern theorem prover and programming language based on dependent type theory.

The goal of this repository is to demonstrate how mathematical reasoning and software verification can be expressed and proven formally using Lean.

Formal methods are widely used in **critical and large-scale systems**, especially in:
- embedded systems
- aerospace and automotive software
- security-critical applications
- industrial verification processes (e.g., STQB-related methodologies and model-based testing approaches)

In such systems, correctness is not optional — it must be proven, not assumed.

---

## Why Formal Methods?

**In traditional software development, testing only shows the presence of bugs, not their absence.**

Formal methods aim to:
- mathematically prove correctness
- eliminate logical errors early
- model system behavior precisely
- ensure reliability in safety-critical environments

---

## Contents

| Module | What is proved | Technique |
|--------|---------------|-----------|
| **Gauss Summation** | `2 * (1 + 2 + … + n) = n * (n + 1)` | Recursive definition, proved by induction |
| **Fibonacci** | Recurrence consistency `fib(n+2) = fib(n+1) + fib(n)` | Recursive definition, proved by reflexivity |
| **Vector & List Properties** | `map` preserves length, `map` composition, `foldl` distributes over append, type-indexed `Vec` with map-map fusion | Structural induction on lists and custom vectors |
| **Formalized Neuron** | Dot product, threshold activation, zero-weight theorem | Definition + `simp`-based proofs |

---

## Purpose

This project is part of my learning journey in formal methods, mathematical logic, and theorem proving systems.
