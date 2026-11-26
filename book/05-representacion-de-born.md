# 5. La representación de Born y la evolución unitaria

> Código: `Stochastic/Unistochastic.lean`, `Quantum/UnitaryProcess.lean`

## La idea física

¿Cómo conectamos un proceso estocástico con la mecánica cuántica? Con la regla de Born.
Si el sistema empieza en la configuración $j$, su estado cuántico es el vector de base
$|j\rangle$. Después de un tiempo $t$ es $U(t)|j\rangle$, y la probabilidad de encontrarlo
en $i$ es

$$\Gamma_{ij}(t) = |\langle i|U(t)|j\rangle|^2 = |U_{ij}(t)|^2.$$

Barandes da vuelta la lectura habitual. Esta fórmula no describe "lo que pasa al medir",
sino **las probabilidades de transición del proceso estocástico subyacente**.

## La matemática

**Definición (representación de Born).** Una matriz compleja $\Theta$ es una
representación de Born de $\Gamma$ si $\Gamma_{ij} = |\Theta_{ij}|^2$ para todos $i,j$.

**Definición.** $\Gamma$ es **uniestocástica** si tiene una representación de Born
*unitaria*.

**Lema.** Si $U$ es unitaria, sus columnas son vectores unitarios:
$\sum_i |U_{ij}|^2 = 1$.

*Demostración.* $U^\dagger U = \mathbb{1}$. La entrada $(j,j)$ es
$\sum_i \overline{U_{ij}}\,U_{ij} = \sum_i |U_{ij}|^2 = 1$. $\blacksquare$

**Corolario.** Toda matriz uniestocástica es estocástica. Las entradas son módulos al
cuadrado, así que son $\geq 0$, y el lema da que las columnas suman 1.

**Teorema (de lo cuántico a lo estocástico).** Si $U(t)$ es unitaria para todo $t$ y
$U(0)=\mathbb{1}$, entonces $\Gamma_{ij}(t) = |U_{ij}(t)|^2$ define un proceso
estocástico generalizado.

*Demostración.* Por el corolario, cada $\Gamma(t)$ es estocástica. Además
$\Gamma_{ij}(0) = |\delta_{ij}|^2 = \delta_{ij}$. $\blacksquare$

**Advertencia.** No toda matriz estocástica es uniestocástica. El ejemplo clásico es la
matriz $3\times 3$
$$\tfrac{1}{2}\begin{pmatrix}1&1&0\\0&1&1\\1&0&1\end{pmatrix},$$
que no lo es. Por eso el teorema de Barandes en la dirección inversa necesita, en
general, un espacio de configuraciones **más grande**. Lo veremos en el capítulo 8.

## En Lean

```lean
def IsBornRep (Γ : Matrix n n ℝ) (Θ : Matrix n n ℂ) : Prop :=
  ∀ i j, Γ i j = ‖Θ i j‖ ^ 2

def IsUnistochastic (Γ : Matrix n n ℝ) : Prop :=
  ∃ U ∈ Matrix.unitaryGroup n ℂ, IsBornRep Γ U
```

`‖z‖` es el módulo de un número complejo. El lema de las columnas:

```lean
theorem unitary_col_normSq_sum {U : Matrix n n ℂ} (hU : U ∈ Matrix.unitaryGroup n ℂ)
    (j : n) : ∑ i, ‖U i j‖ ^ 2 = 1 := by
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.mp hU) j) j
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq, Complex.star_def,
    Complex.conj_mul'] at h
  exact_mod_cast h
```

Paso a paso:
1. `mem_unitaryGroup_iff'` convierte "$U$ es unitaria" en $U^\dagger U = \mathbb{1}$, y
   `congrFun` dos veces se queda con la entrada $(j,j)$.
2. `simp only [...]` desarrolla esa entrada: el producto de matrices es una suma,
   $\overline{z}z = |z|^2$ y $\mathbb{1}_{jj} = 1$.
3. Queda $\sum_i |U_{ij}|^2 = 1$ como igualdad *en $\mathbb{C}$*. `exact_mod_cast` la
   baja a $\mathbb{R}$.

Esta demostración la hicimos en el proyecto. Al principio estaba como `sorry` y la
dejamos de *good first issue*.

El teorema principal del capítulo es una **definición** con demostraciones adentro:

```lean
noncomputable def ofUnitary (U : ℝ → Matrix n n ℂ) (hU : ∀ t, U t ∈ Matrix.unitaryGroup n ℂ)
    (h0 : U 0 = 1) : GenStochasticProcess n where
  Γ t := Matrix.of fun i j => ‖U t i j‖ ^ 2
  stochastic t _ := (isUnistochastic_normSq (hU t)).mem_colStochastic
  init := by
    ext i j
    by_cases h : i = j <;> simp [h0, Matrix.one_apply, h]
```

Que Lean acepte `ofUnitary` *es* la demostración del teorema: para construir un
`GenStochasticProcess` hay que probar `stochastic` e `init`. `noncomputable` indica que
el módulo de un complejo no se puede "calcular" con exactitud en una computadora, lo
cual es irrelevante para las demostraciones.

## Ejercicios

1. (Papel) Demostrá que la matriz $3\times 3$ de la advertencia no es uniestocástica.
   Pista: como $U_{21} = 0$ y $U_{32} = 0$, el producto interno de las columnas 1 y 2 de
   $U$ tiene un único término que no se anula, y no puede valer cero.
2. (Papel) Si $\Theta$ es una representación de Born de $\Gamma$ y $D$ es una matriz
   diagonal de fases ($|D_{ii}|=1$), ¿$D\Theta$ y $\Theta D$ también lo son? Esta es la
   **libertad de gauge** de la representación.
3. (Lean) Demostrá que toda matriz estocástica tiene *alguna* representación de Born.
   Pista: $\Theta_{ij} = \sqrt{\Gamma_{ij}}$. Está en el roadmap.
