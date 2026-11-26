# 4. Procesos indivisibles y eventos de división

> Código: `IndivisibleStochasticMechanics/Stochastic/Indivisible.lean`

## La idea física

En un curso de probabilidad, un proceso estocástico suele ser **markoviano**: el futuro
depende solo del presente. Entonces para ir de $0$ a $t$ podemos parar en cualquier
$t'$ intermedio:

$$\Gamma(t\leftarrow 0) = \Gamma(t\leftarrow t')\,\Gamma(t'\leftarrow 0), \qquad 0 \le t' \le t,$$

con $\Gamma(t\leftarrow t')$ estocástica. Esto se llama **divisibilidad**.

La observación clave de Barandes es que **nada en la teoría de la probabilidad obliga a
que eso pase**. Un proceso queda definido por sus probabilidades condicionales respecto
del instante inicial, $\Gamma(t\leftarrow 0)$. Que además existan $\Gamma(t\leftarrow t')$
estocásticas que las compongan es una propiedad *adicional*, que puede cumplirse o no.

- Si se cumple para un instante concreto $t'$, decimos que $t'$ es un **evento de
  división**: el proceso "se reinicia" ahí.
- Si no se cumple en todos los instantes, el proceso es **indivisible**.

Barandes sostiene que los sistemas cuánticos son justamente procesos indivisibles, y que
los eventos de división aparecen físicamente cuando hay **decoherencia** o **medición**.

## La matemática

**Definición (proceso estocástico generalizado).** Es una familia de matrices
$\Gamma(t) := \Gamma(t\leftarrow 0)$, para $t \geq 0$, tal que:
1. $\Gamma(t)$ es estocástica para todo $t \geq 0$;
2. $\Gamma(0) = \mathbb{1}$: en tiempo cero no pasó nada.

**Definición (evento de división).** $t' \geq 0$ es un evento de división si existe una
familia $\Delta(t)$ con $\Delta(t)$ estocástica y
$$\Gamma(t) = \Delta(t)\,\Gamma(t') \qquad \text{para todo } t \ge t'.$$
Acá $\Delta(t)$ cumple el papel de $\Gamma(t \leftarrow t')$.

**Definición.** El proceso es **divisible** si todo $t' \geq 0$ es un evento de
división, e **indivisible** si no lo es.

**Proposición.** $t' = 0$ siempre es un evento de división.

*Demostración.* Tomamos $\Delta(t) = \Gamma(t)$. Como $\Gamma(0) = \mathbb{1}$, se cumple
$\Gamma(t) = \Gamma(t)\cdot\mathbb{1}$. $\blacksquare$

## En Lean

```lean
structure GenStochasticProcess (n : Type*) [Fintype n] [DecidableEq n] where
  Γ : ℝ → Matrix n n ℝ
  stochastic : ∀ t, 0 ≤ t → Γ t ∈ colStochastic ℝ n
  init : Γ 0 = 1
```

Una `structure` que no es `Prop` es un "objeto con datos". Un proceso *es* una función
`Γ` de los tiempos en las matrices, *junto con* las demostraciones de que es estocástica
y de que empieza en la identidad. No se puede construir un proceso sin dar esas
demostraciones.

```lean
def IsDivisionEvent (t' : ℝ) : Prop :=
  0 ≤ t' ∧ ∃ Δ : ℝ → Matrix n n ℝ,
    ∀ t, t' ≤ t → Δ t ∈ colStochastic ℝ n ∧ P.Γ t = Δ t * P.Γ t'

def IsDivisible : Prop := ∀ t', 0 ≤ t' → P.IsDivisionEvent t'
def IsIndivisible : Prop := ¬ P.IsDivisible
```

La traducción es literal. `¬` es "no", `∃` es "existe" y `∀` es "para todo".

```lean
theorem isDivisionEvent_zero : P.IsDivisionEvent 0 :=
  ⟨le_rfl, P.Γ, fun t ht => ⟨P.stochastic t ht, by simp [P.init]⟩⟩
```

Los corchetes angulares `⟨ ... ⟩` arman la demostración pieza por pieza, en el mismo
orden que la definición:
- `le_rfl` prueba $0 \le 0$;
- `P.Γ` es el testigo $\Delta$;
- para cada $t$, `P.stochastic t ht` prueba que $\Delta(t)$ es estocástica, y
  `by simp [P.init]` prueba $\Gamma(t) = \Gamma(t)\,\Gamma(0)$ usando $\Gamma(0)=\mathbb{1}$.

## Una sutileza: lo que la definición *no* dice

Un proceso generalizado especifica solamente $\Gamma(t\leftarrow 0)$. **No** especifica
probabilidades conjuntas en varios instantes, como $P(i \text{ en } t_2,\ k \text{ en } t_1 \mid j \text{ en } 0)$.
Es una decisión deliberada de Barandes, y es una de las preguntas abiertas de la Parte IV.

## Ejercicios

1. (Papel) Mostrá que si $\Gamma(t) = e^{tL}$ para una matriz $L$ con columnas que suman
   cero y entradas fuera de la diagonal no negativas (un *generador de Markov*), el
   proceso es divisible.
2. (Papel) Si $\Gamma(t')$ es invertible, ¿cuál es el único candidato posible para
   $\Delta(t)$? ¿Qué condición tiene que cumplir para que $t'$ sea un evento de división?
3. (Lean) Demostrá que si $\Gamma(t) = \mathbb{1}$ para todo $t$, el proceso es divisible.
