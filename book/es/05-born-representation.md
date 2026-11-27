# 5. La representación de Born y la evolución unitaria

> Código: `Stochastic/Unistochastic.lean`, `Quantum/UnitaryProcess.lean`, `Quantum/Hamiltonian.lean`

## La idea física

¿Cómo conectamos un proceso estocástico con la mecánica cuántica? Con la regla de Born.
Si el sistema empieza en la configuración $j$, su estado cuántico es el vector de base
$|j\rangle$. Después de un tiempo $t$ es $U(t)|j\rangle$, y la probabilidad de encontrarlo
en $i$ es

$$\Gamma_{ij}(t) = |\langle i|U(t)|j\rangle|^2 = |U_{ij}(t)|^2.$$

La fórmula es la regla de Born ([Born, 1926](https://doi.org/10.1007/BF01397477)).
Barandes ([Barandes, 2023a](https://arxiv.org/abs/2302.10778)) da vuelta la lectura habitual. Esta fórmula no describe "lo que pasa al medir",
sino **las probabilidades de transición del proceso estocástico subyacente**.

## La matemática

**Definición (representación de Born, de [Barandes, 2023b](https://arxiv.org/abs/2309.03085)).** Una matriz compleja $\Theta$ es una
representación de Born de $\Gamma$ si $\Gamma_{ij} = |\Theta_{ij}|^2$ para todos $i,j$.

**Definición.** $\Gamma$ es **uniestocástica** si tiene una representación de Born
*unitaria*. Es un concepto clásico del álgebra lineal (ver, por ejemplo,
[Życzkowski, Słomczyński, Kuś y Sommers, 2003](https://arxiv.org/abs/nlin/0112036)).

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
que no lo es. Es un ejemplo conocido de la literatura sobre matrices uniestocásticas, y
el ejercicio 1 pide demostrarlo. Por eso el teorema de Barandes en la dirección inversa necesita, en
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

## De dónde sale $U(t)$: el hamiltoniano

`ofUnitary` acepta *cualquier* familia unitaria con $U(0) = \mathbb{1}$. En la mecánica
cuántica de libro de texto la familia sale de un hamiltoniano: una matriz hermítica $H$
($H^\dagger = H$), con

$$U(t) = e^{-itH} = \sum_{k \geq 0} \frac{(-itH)^k}{k!} \qquad (\hbar = 1),$$

la solución de la ecuación de Schrödinger $i\,\dot U = H U$ con $U(0) = \mathbb{1}$ (ver,
por ejemplo, [Nielsen y Chuang, 2000](https://doi.org/10.1017/CBO9780511976667),
§2.2.2). Tres hechos la convierten en una entrada válida para `ofUnitary`:

1. $U(0) = e^0 = \mathbb{1}$.
2. **Ley de grupo:** $U(s+t) = U(s)\,U(t)$, porque $sH$ y $tH$ conmutan.
3. **Unitariedad:** $U(t)^\dagger = e^{+itH^\dagger} = e^{itH} = U(-t)$, así que
   $U(t)^\dagger U(t) = U(-t+t) = \mathbb{1}$.

En Lean (`Quantum/Hamiltonian.lean`) la exponencial es `NormedSpace.exp` de Mathlib:

```lean
noncomputable def hamiltonianEvolution (H : Matrix n n ℂ) (t : ℝ) : Matrix n n ℂ :=
  exp ((-(t : ℂ) * I) • H)

theorem hamiltonianEvolution_add (H : Matrix n n ℂ) (s t : ℝ) :
    hamiltonianEvolution H (s + t) = hamiltonianEvolution H s * hamiltonianEvolution H t

theorem hamiltonianEvolution_mem_unitaryGroup {H : Matrix n n ℂ} (hH : H.IsHermitian)
    (t : ℝ) : hamiltonianEvolution H t ∈ unitaryGroup n ℂ

noncomputable def GenStochasticProcess.ofHamiltonian (H : Matrix n n ℂ)
    (hH : H.IsHermitian) : GenStochasticProcess n
```

La prueba de unitariedad son exactamente los tres pasos de arriba:
`Matrix.exp_conjTranspose` mete la $\dagger$ adentro de la exponencial, `hH.eq` reemplaza
$H^\dagger$ por $H$, y `Matrix.exp_add_of_commute` da la ley de grupo. Así, todo
hamiltoniano de dimensión finita da un proceso estocástico generalizado.

Fijate qué es lo que **no** se traslada. $U$ cumple la ley de grupo, pero
$\Gamma_{ij}(t) = |U_{ij}(t)|^2$ en general no: $\Gamma(s+t) \neq \Gamma(s)\,\Gamma(t)$.
Tomar módulos al cuadrado destruye la ley de composición, y esa brecha es justamente la
indivisibilidad. El capítulo siguiente lo muestra en el ejemplo más simple.

## Ejercicios

1. (Papel) Demostrá que la matriz $3\times 3$ de la advertencia no es uniestocástica.
   Pista: como $U_{21} = 0$ y $U_{32} = 0$, el producto interno de las columnas 1 y 2 de
   $U$ tiene un único término que no se anula, y no puede valer cero.
2. (Papel) Si $\Theta$ es una representación de Born de $\Gamma$ y $D$ es una matriz
   diagonal de fases ($|D_{ii}|=1$), ¿$D\Theta$ y $\Theta D$ también lo son? Esta es la
   **libertad de gauge** de la representación.
3. (Lean) Demostrá que toda matriz estocástica tiene *alguna* representación de Born.
   Pista: $\Theta_{ij} = \sqrt{\Gamma_{ij}}$. Está en el roadmap.
4. (Lean) Mostrá que un hamiltoniano diagonal da un proceso trivial: si $H$ es diagonal y
   hermítica, entonces `(GenStochasticProcess.ofHamiltonian H hH).Γ t = 1` para todo $t$.
   Pista: `Matrix.exp_diagonal`. Físicamente, las configuraciones son autoestados de la
   energía, que solo adquieren fases.
