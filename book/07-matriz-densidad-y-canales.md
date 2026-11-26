# 7. Matrices densidad y canales cuánticos

> Código: `IndivisibleStochasticMechanics/Quantum/DensityMatrix.lean`,
> `IndivisibleStochasticMechanics/Quantum/Channel.lean`

Hasta ahora trabajamos con evoluciones unitarias y vectores de estado. La mecánica cuántica
de libro usa dos herramientas más generales: la **matriz densidad**, para estados mezcla, y
los **canales cuánticos**, para sistemas abiertos, ruido y pérdida de información. Este
capítulo muestra que las dos tienen su contraparte estocástica exacta.

## Parte A: la matriz densidad como objeto derivado

### La idea física

En la formulación usual, la matriz densidad $\rho$ es *el* estado del sistema. En la de
Barandes es una **herramienta de cálculo** que se construye a partir de dos ingredientes:
la representación de Born $\Theta$ y la distribución de probabilidad $p$ sobre las
configuraciones iniciales:

$$\rho = \Theta\,\mathrm{diag}(p)\,\Theta^\dagger .$$

### La matemática

**Teorema.** Si $\Gamma_{ij} = |\Theta_{ij}|^2$, entonces la diagonal de $\rho$ es la
distribución estocástica:
$$\rho_{ii} = \sum_j \Gamma_{ij}\,p_j = (\Gamma p)_i .$$

*Demostración.*
$$\rho_{ii} = \sum_j \Theta_{ij}\,p_j\,\overline{\Theta_{ij}} = \sum_j |\Theta_{ij}|^2 p_j = \sum_j \Gamma_{ij}\,p_j. \qquad\blacksquare$$

**Teorema.** Si $\Gamma$ es estocástica y $p$ es una distribución, entonces $\rho$ es una
matriz densidad legítima: es semidefinida positiva y tiene traza 1.

*Demostración.* $\mathrm{diag}(p)$ es semidefinida positiva porque $p_j \ge 0$, y
conjugar por $\Theta$ preserva esa propiedad. Para la traza,
$\mathrm{tr}\,\rho = \sum_i \rho_{ii} = \sum_i (\Gamma p)_i = 1$ por el capítulo 3.
$\blacksquare$

**Corolario.** Para un proceso unitario, $\rho(t) = U(t)\,\mathrm{diag}(p_0)\,U(t)^\dagger$
es *exactamente* la evolución de libro de un estado mezcla, y su diagonal es la
distribución estocástica en el instante $t$.

### Lo que dice la diagonal y lo que dicen los demás elementos

La diagonal de $\rho$ contiene **toda** la información probabilística sobre dónde está el
sistema. Los elementos fuera de la diagonal (las *coherencias*) no son probabilidades de
nada. Son la huella de la indivisibilidad: la información que el sistema necesita para
"recordar" su configuración inicial más adelante.

**Ejemplo: el qubit del capítulo 6.** Si empieza en la configuración 0, entonces
$p_0 = (1, 0)$ y

$$\rho(t) = \begin{pmatrix}\cos^2 t & i\cos t\sin t\\ -i\cos t\sin t & \sin^2 t\end{pmatrix}.$$

En $t = \pi/4$ la diagonal es $(1/2, 1/2)$: mezcla total. Pero las coherencias valen
$\pm i/2$, el máximo posible. En una mezcla clásica serían cero. Esa diferencia es
justamente lo que permite que en $t = \pi/2$ el sistema "vuelva" a una configuración
definida.

## Parte B: canales cuánticos

### La idea física

Un **canal cuántico** describe cualquier evolución física posible de un sistema, incluso
cuando interactúa con un entorno al que no tenemos acceso. Se escribe en **forma de Kraus**:
$$\rho \;\mapsto\; \sum_k K_k\,\rho\,K_k^\dagger, \qquad \sum_k K_k^\dagger K_k = \mathbb{1}.$$
Una evolución unitaria es el caso de un único operador de Kraus, $K = U$.

### La matemática

**Teorema (de lo cuántico a lo estocástico).** Todo canal induce una matriz estocástica:
$$\Gamma_{ij} = \sum_k |(K_k)_{ij}|^2 .$$

*Demostración.* Cada columna suma
$\sum_i\sum_k |(K_k)_{ij}|^2 = \sum_k (K_k^\dagger K_k)_{jj} = \mathbb{1}_{jj} = 1$.
$\blacksquare$

**Teorema.** Aplicado a una mezcla de configuraciones $\mathrm{diag}(p)$, el canal produce
una matriz con diagonal $\Gamma p$.

**Teorema (de lo estocástico a lo cuántico).** Toda matriz estocástica es la matriz de
transición de algún canal cuántico. Basta tomar los operadores de Kraus "clásicos"
$$K_{(a,b)} = \sqrt{\Gamma_{ab}}\;|a\rangle\langle b| ,$$
que llevan la configuración $b$ a la $a$ con amplitud $\sqrt{\Gamma_{ab}}$.

*Demostración.*
$\sum_{a,b} K_{(a,b)}^\dagger K_{(a,b)} = \sum_{a,b} \Gamma_{ab}\,|b\rangle\langle b| = \sum_b \big(\textstyle\sum_a \Gamma_{ab}\big)|b\rangle\langle b| = \mathbb{1}$,
porque las columnas suman 1. Además,
$\sum_{a,b} |(K_{(a,b)})_{ij}|^2 = \Gamma_{ij}$. $\blacksquare$

**Conclusión.** Para las estadísticas de transición desde el instante inicial, los canales
cuánticos y las matrices estocásticas son lo mismo. Comparado con el capítulo 8, este
resultado no necesita agrandar el espacio de configuraciones, porque los canales ya
incluyen implícitamente un entorno.

## En Lean

```lean
noncomputable def bornDensity (Θ : Matrix n n ℂ) (p : n → ℝ) : Matrix n n ℂ :=
  Θ * diagonal (fun j => (p j : ℂ)) * Θᴴ

theorem bornDensity_apply_self {Γ : Matrix n n ℝ} {Θ : Matrix n n ℂ} (h : IsBornRep Γ Θ)
    (p : n → ℝ) (i : n) : bornDensity Θ p i i = ((Γ *ᵥ p) i : ℂ)
```

Para la positividad usamos `PosSemidef` de Mathlib. En ℂ hay que activar el orden parcial
con `open ComplexOrder`, porque Mathlib no lo activa por defecto: el orden de los números
complejos no es el que uno espera.

```lean
def IsKrausFamily (K : κ → Matrix n n ℂ) : Prop := ∑ k, (K k)ᴴ * K k = 1

noncomputable def krausTransition (K : κ → Matrix n n ℂ) : Matrix n n ℝ :=
  Matrix.of fun i j => ∑ k, ‖K k i j‖ ^ 2

theorem IsKrausFamily.krausTransition_mem_colStochastic (hK : IsKrausFamily K) :
    krausTransition K ∈ colStochastic ℝ n

theorem krausTransition_classicalKraus (hΓ : Γ ∈ colStochastic ℝ n) :
    krausTransition (classicalKraus Γ) = Γ
```

Un detalle técnico útil: la identidad "norma al cuadrado de una columna = entrada
diagonal de $A^\dagger A$" aparece una y otra vez. La pusimos en `ForMathlib/` como
`Matrix.sum_norm_sq_col_eq_conjTranspose_mul_self`.

## Ejercicios

1. (Papel) Calculá $\rho(t)$ para el qubit con $p_0 = (1/2, 1/2)$. ¿Hay coherencias? ¿Qué
   te dice eso sobre si $\pi/4$ es un evento de división para esa condición inicial?
2. (Papel) El *canal de desfasaje* tiene $K_0 = \sqrt{1-q}\,\mathbb{1}$ y
   $K_1 = \sqrt{q}\,\sigma_z$. Calculá su $\Gamma$. ¿Qué le hace a las coherencias?
3. (Papel) Mostrá que una composición de canales es un canal. ¿Por qué eso no contradice
   que los procesos indivisibles no se descomponen en pasos?
4. (Lean) Formalizá el ejercicio 2.
