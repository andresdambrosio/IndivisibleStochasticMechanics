# 3. Probabilidades y matrices estocásticas

> Código: `IndivisibleStochasticMechanics/Stochastic/Basic.lean`

## La idea física

El material de este capítulo es probabilidad estándar. La convención por columnas es la
de Barandes ([Barandes, 2023a](https://arxiv.org/abs/2302.10778)).

El sistema tiene un **espacio de configuraciones** finito $\mathcal{C} = \{1, \dots, N\}$.
Pueden ser las posiciones de una partícula en una red, los dos estados de un bit, etc.
En cada instante el sistema está en *una* configuración. No sabemos cuál, así que
describimos nuestro conocimiento con una distribución de probabilidad $p_i(t)$.

La dinámica viene dada por las **probabilidades de transición**

$$\Gamma_{ij}(t) = P(\text{estar en } i \text{ en el instante } t \mid \text{estaba en } j \text{ en el instante } 0).$$

## La matemática

**Definición (distribución de probabilidad).** $p \in \mathbb{R}^N$ es una distribución
si $p_i \geq 0$ para todo $i$ y $\sum_i p_i = 1$.

**Definición (matriz estocástica por columnas).** $\Gamma \in \mathbb{R}^{N\times N}$ es
estocástica si $\Gamma_{ij} \geq 0$ para todos $i,j$ y cada columna suma uno:
$\sum_i \Gamma_{ij} = 1$ para todo $j$.

La condición sobre las columnas dice que, partiendo de $j$, el sistema termina en
*alguna* configuración con probabilidad 1.

Por la ley de probabilidad total, la distribución evoluciona así:

$$p_i(t) = \sum_j \Gamma_{ij}(t)\, p_j(0), \qquad\text{es decir}\qquad p(t) = \Gamma(t)\,p(0).$$

**Proposición.** Si $\Gamma$ es estocástica y $p$ es una distribución, entonces
$\Gamma p$ es una distribución.

*Demostración.* La no negatividad sale de que es una suma de productos de números no
negativos. Para la suma:
$$\sum_i (\Gamma p)_i = \sum_i \sum_j \Gamma_{ij}\,p_j = \sum_j p_j \underbrace{\sum_i \Gamma_{ij}}_{=1} = \sum_j p_j = 1. \qquad\blacksquare$$

**Hecho.** El producto de dos matrices estocásticas es estocástico, y la identidad
es estocástica. En lenguaje algebraico, las matrices estocásticas forman un
**monoide**. Físicamente, la identidad es "no pasa nada" y el producto es "encadenar dos
evoluciones".

## En Lean

La distribución de probabilidad la definimos nosotros:

```lean
structure IsProbDist (p : n → ℝ) : Prop where
  nonneg : ∀ i, 0 ≤ p i
  sum_eq_one : ∑ i, p i = 1
```

Para las matrices estocásticas usamos la definición de Mathlib: `Γ ∈ colStochastic ℝ n`.
Mathlib la define como un `Submonoid` de las matrices, así que el "Hecho" de arriba ya
viene incluido: `one_mem` y `mul_mem`.

La proposición queda en cuatro líneas:

```lean
theorem IsProbDist.mulVec [DecidableEq n] {Γ : Matrix n n ℝ} (hΓ : Γ ∈ colStochastic ℝ n)
    {p : n → ℝ} (hp : IsProbDist p) : IsProbDist (Γ *ᵥ p) where
  nonneg := nonneg_mulVec_of_mem_colStochastic hΓ hp.nonneg
  sum_eq_one := by rw [sum_mulVec_of_mem_colStochastic hΓ, hp.sum_eq_one]
```

- `Γ *ᵥ p` es el producto matriz-vector.
- `nonneg := ...` demuestra la primera condición con un lema de Mathlib.
- `sum_eq_one := ...` usa otro lema de Mathlib, que dice que $\sum_i (\Gamma p)_i = \sum_i p_i$,
  y después la hipótesis $\sum_i p_i = 1$.

Es la misma demostración que en papel. La parte del intercambio de sumatorias ya la
hizo alguien en Mathlib.

## Ejercicios

1. (Papel) Demostrá que si $\Gamma$ es estocástica, entonces $0 \leq \Gamma_{ij} \leq 1$.
   (En Mathlib: `le_one_of_mem_colStochastic`.)
2. (Papel) ¿Por qué Barandes usa la convención *por columnas* y no *por filas*? ¿Qué
   cambia en la fórmula $p(t) = \Gamma(t)p(0)$?
3. (Lean) Enunciá y demostrá que toda matriz de permutación es estocástica. Pista: Mathlib
   ya tiene `permMatrix_mem_colStochastic`. Buscala y usala.
