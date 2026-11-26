# 2. Lean para físicos, en lo mínimo indispensable

Este capítulo no es un curso de Lean. Su objetivo es que puedas **leer** el código del
proyecto y modificarlo un poco. Para profundizar, el mejor recurso es
[*Mathematics in Lean*](https://leanprover-community.github.io/mathematics_in_lean/), de
Jeremy Avigad y Patrick Massot.

## Tres ideas

**1. Todo tiene un tipo.** `ℝ` es el tipo de los números reales, `ℂ` el de los complejos
y `Matrix n n ℝ` el de las matrices reales con filas y columnas indexadas por `n`. Un
"espacio de configuraciones finito" es simplemente un tipo `n` con la propiedad
`[Fintype n]`: tiene una cantidad finita de elementos.

**2. Las proposiciones también son tipos, y las demostraciones son sus elementos.**
Escribir

```lean
theorem foo : 2 + 2 = 4 := by norm_num
```

significa "`foo` es una demostración de `2 + 2 = 4`, y se construye con la táctica
`norm_num`". Si Lean acepta el archivo, la demostración es correcta.

**3. Las tácticas son los pasos de la demostración.** Después de `by` se escribe una
secuencia de pasos. Los más comunes en este proyecto son:

| Táctica | Qué hace |
|---|---|
| `simp [lemas]` | simplifica usando reglas de reescritura |
| `rw [h]` | reescribe usando la igualdad `h` |
| `linarith` | cierra objetivos que son desigualdades o igualdades lineales |
| `positivity` | demuestra que algo es $\geq 0$ o $> 0$ |
| `ext i j` | para probar que dos matrices son iguales, prueba que coinciden entrada a entrada |
| `fin_cases i` | divide en casos según los valores posibles de `i : Fin 2` |
| `exact h` | "esto es exactamente `h`" |

## Cómo se lee una definición

```lean
structure IsProbDist (p : n → ℝ) : Prop where
  nonneg : ∀ i, 0 ≤ p i
  sum_eq_one : ∑ i, p i = 1
```

En palabras: "Una función $p$ de las configuraciones en los reales *es una distribución
de probabilidad* si cumple dos cosas: $p_i \geq 0$ para todo $i$, y
$\sum_i p_i = 1$". Una `structure` de tipo `Prop` agrupa varias condiciones en una sola.

## Mathlib

[Mathlib](https://github.com/leanprover-community/mathlib4) es la gran biblioteca de
matemática de Lean, escrita por cientos de colaboradores
([The mathlib Community, 2020](https://arxiv.org/abs/1910.09336)). No reinventamos nada que ya esté en
ella: matrices, números complejos, grupos unitarios, trigonometría, teoría de la medida.
Por ejemplo, usamos su definición de matriz estocástica por columnas
(`Matrix.colStochastic`), y así heredamos todos sus teoremas.

## Estructura de un archivo del proyecto

```lean
module                          -- usa el sistema de módulos de Lean
public import Mathlib           -- qué otros archivos necesita

/-! # Título
Explicación en prosa, referencias a los papers. -/

@[expose] public section        -- lo que sigue es visible para quien importe el archivo

namespace ISM                   -- todas nuestras definiciones viven en `ISM.`
...
end ISM
```

## `sorry`

`sorry` es una demostración "en blanco": Lean la acepta, pero marca el archivo con un
aviso. Sirve para escribir primero los enunciados y probarlos después. En este proyecto,
la rama `main` no debe contener ningún `sorry`.

## Ejercicios

1. Instalá Lean ([lean-lang.org/install](https://lean-lang.org/install)), cloná el repositorio y ejecutá
   `lake build`.
2. Abrí `IndivisibleStochasticMechanics/Stochastic/Basic.lean` en VS Code con la
   extensión de Lean. Poné el cursor dentro de una demostración y mirá el panel *Lean
   Infoview*: muestra el objetivo que queda por demostrar en cada paso.
