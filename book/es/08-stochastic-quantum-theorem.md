# 8. El teorema estocástico-cuántico: de procesos a espacios de Hilbert

> Código: `IndivisibleStochasticMechanics/Quantum/Dilation.lean`,
> `IndivisibleStochasticMechanics/ForMathlib/Matrix/Unitary.lean`

En el capítulo 5 vimos una dirección de la correspondencia: toda evolución unitaria
define un proceso estocástico. Este capítulo demuestra la otra: **todo proceso
estocástico se puede ver como un sistema cuántico**. El teorema es de Barandes
([Barandes, 2023b](https://arxiv.org/abs/2309.03085)). Con las dos direcciones juntas
obtenemos el primer teorema de equivalencia verificado del proyecto.

## El obstáculo

Lo más directo sería buscar, para cada $\Gamma$ estocástica, una unitaria $U$ con
$\Gamma_{ij} = |U_{ij}|^2$. Pero en el capítulo 5 vimos que **no siempre existe**: la
matriz
$$\tfrac{1}{2}\begin{pmatrix}1&1&0\\0&1&1\\1&0&1\end{pmatrix}$$
es estocástica y no es uniestocástica. En el mismo espacio de configuraciones no hay
evolución unitaria que la produzca.

## La salida: agrandar el sistema

La idea, central en mecánica cuántica, es que un sistema que no evoluciona de forma
unitaria puede ser **parte** de un sistema más grande que sí lo hace. Agregamos un
**entorno** con configuraciones $e \in \mathcal{E}$, preparado en un estado fijo $e_0$, y
pedimos que

$$\Gamma_{ij} = \sum_{e \in \mathcal{E}} \big|U_{(i,e),(j,e_0)}\big|^2 .$$

En palabras: $\Gamma_{ij}$ es la probabilidad de encontrar al **sistema** en $i$, *haga lo
que haga el entorno*, si empezó en $j$ y el entorno en $e_0$. Esto se llama una
**dilatación unitaria** de $\Gamma$. Es la misma idea que el teorema de dilatación de Stinespring
([Stinespring, 1955](https://doi.org/10.2307/2032342)).

## La matemática

**Definición.** $U$ es una dilatación unitaria de $\Gamma$, con entorno $\mathcal{E}$ y
estado inicial $e_0$, si $U$ es unitaria en $\mathcal{C}\times\mathcal{E}$ y
$\Gamma_{ij} = \sum_e |U_{(i,e),(j,e_0)}|^2$ para todos $i, j$.

**Proposición (de lo cuántico a lo estocástico).** Si $U$ es una dilatación unitaria de
$\Gamma$, entonces $\Gamma$ es estocástica.

*Demostración.* Las entradas son sumas de módulos al cuadrado, así que son $\ge 0$. La
columna $j$ suma
$$\sum_i \Gamma_{ij} = \sum_i\sum_e |U_{(i,e),(j,e_0)}|^2 = \sum_{(i,e)} |U_{(i,e),(j,e_0)}|^2 = 1,$$
porque es la norma al cuadrado de la columna $(j,e_0)$ de una matriz unitaria. $\blacksquare$

**Teorema (de lo estocástico a lo cuántico).** Toda matriz estocástica $\Gamma$ tiene una
dilatación unitaria. Basta un entorno con $N+1$ configuraciones.

*Demostración.* Esta construcción concreta es nuestra. Es una dilatación directa del tipo
de Stinespring, y no necesariamente coincide con la de Barandes, que pasa por operadores
de Kraus y una dilatación de Stinespring de dimensión a lo sumo $N^3$
([Barandes, 2026](https://arxiv.org/abs/2602.01043), §5); la nuestra tiene dimensión
$N(N+1)$. Tomamos como
entorno $\mathcal{E} = \{\varnothing\} \cup \mathcal{C}$, con
estado inicial $e_0 = \varnothing$. En Lean esto es `Option n`, y $\varnothing$ es `none`.
Para cada configuración inicial $j$ definimos el vector
$$v_j = \sum_i \sqrt{\Gamma_{ij}}\; |i\rangle \otimes |j\rangle_{\mathcal{E}} .$$
Físicamente: el sistema va a $i$ con amplitud $\sqrt{\Gamma_{ij}}$, y el entorno **anota**
de dónde partió.

*Paso 1: los $v_j$ son ortonormales.*
$$\langle v_j, v_k\rangle = \sum_i \sqrt{\Gamma_{ij}}\sqrt{\Gamma_{ik}}\;\langle j|k\rangle_{\mathcal{E}} = \delta_{jk}\sum_i \Gamma_{ij} = \delta_{jk}.$$
Lo notable es que **la condición de normalización de una matriz estocástica (las
columnas suman 1) es exactamente la normalización de los vectores $v_j$**. Y la
ortogonalidad la da el entorno, porque guarda la configuración inicial.

*Paso 2: completar a una unitaria.* Una familia ortonormal siempre se puede completar a
una base ortonormal de todo el espacio. La matriz $U$ cuyas columnas son esa base es
unitaria, y su columna $(j, \varnothing)$ es $v_j$.

*Paso 3: recuperar $\Gamma$.*
$$\sum_e |U_{(i,e),(j,\varnothing)}|^2 = \sum_e |(v_j)_{(i,e)}|^2 = \big|\sqrt{\Gamma_{ij}}\big|^2 = \Gamma_{ij}. \qquad\blacksquare$$

**Corolario (correspondencia estocástico-cuántica en dimensión finita).** Una familia de
matrices $\Gamma(t)$ es estocástica en todo $t \ge 0$ **si y solo si** en todo $t \ge 0$ es
la marginal de una evolución unitaria $U(t)$ del sistema más el entorno.

## Lo que el teorema dice y lo que no

Esta discusión es nuestra. Es el tipo de discusión que la formalización obliga a tener, y por eso también
quedó anotada en `TRUSTED.md`.

- **Lo que dice:** en cada instante, las probabilidades de transición de *cualquier*
  proceso estocástico son las de un sistema cuántico, siempre que se lo vea como parte
  de un sistema más grande.
- **Lo que no dice:** la $U(t)$ se elige **por separado en cada instante**. El teorema no
  garantiza que $U(t)$ sea continua en $t$, ni que $U(0) = \mathbb{1}$, ni que provenga de
  un hamiltoniano. Una versión más fuerte, que pida eso, es la siguiente tarea del
  roadmap.
- **Por qué no es trampa:** la indivisibilidad hace que no se pueda pedir $U(t) = U(t\leftarrow t')U(t')$
  sin más. Las leyes estocásticas se condicionan respecto del instante inicial, y la
  dilatación también.

## En Lean

La definición:

```lean
def IsUnitaryDilation (Γ : Matrix n n ℝ) (U : Matrix (n × m) (n × m) ℂ) (e₀ : m) : Prop :=
  U ∈ unitaryGroup (n × m) ℂ ∧ ∀ i j, Γ i j = ∑ e, ‖U (i, e) (j, e₀)‖ ^ 2
```

El espacio del sistema más el entorno es el producto `n × m`, y sus configuraciones son
pares `(i, e)`.

Los vectores $v_j$:

```lean
noncomputable def dilationVec (Γ : Matrix n n ℝ) (c : n × Option n) :
    EuclideanSpace ℂ (n × Option n) :=
  WithLp.toLp 2 fun a => if a.2 = some c.1 then (Real.sqrt (Γ a.1 c.1) : ℂ) else 0
```

`EuclideanSpace ℂ ι` es $\mathbb{C}^\iota$ con su producto interno, y `WithLp.toLp 2`
convierte una función en un vector de ese espacio. La entrada $(i, e)$ vale
$\sqrt{\Gamma_{ij}}$ si el entorno anotó $j$ ($e = $ `some j`) y $0$ si no.

El paso 2 es un resultado general de álgebra lineal, así que lo pusimos en
`ForMathlib/`, la carpeta de resultados pensados para subir a Mathlib:

```lean
theorem exists_mem_unitaryGroup_of_orthonormal {s : Set ι} {v : ι → EuclideanSpace 𝕜 ι}
    (hv : Orthonormal 𝕜 (s.domRestrict v)) :
    ∃ U ∈ unitaryGroup ι 𝕜, ∀ j ∈ s, ∀ i, U i j = v j i
```

La demostración usa `Orthonormal.exists_orthonormalBasis_extension_of_card_eq`, que
completa la familia a una base, y `toMatrix_orthonormalBasis_mem_unitary`, que dice que
la matriz de una base ortonormal es unitaria. Las dos ya estaban en Mathlib.

Con todo eso, el teorema principal es corto:

```lean
theorem forall_mem_colStochastic_iff_exists_isUnitaryDilation (Γ : ℝ → Matrix n n ℝ) :
    (∀ t, 0 ≤ t → Γ t ∈ colStochastic ℝ n) ↔
      ∃ U : ℝ → Matrix (n × Option n) (n × Option n) ℂ,
        ∀ t, 0 ≤ t → IsUnitaryDilation (Γ t) (U t) none
```

En la dirección "⇒", `choose` elige una dilatación para cada instante: es el axioma de
elección. En la dirección "⇐" se aplica la proposición de lo cuántico a lo estocástico.

Para comprobar que no hay trampas ocultas, en Lean se puede preguntar de qué axiomas
depende un teorema:

```lean
#print axioms ISM.forall_mem_colStochastic_iff_exists_isUnitaryDilation
-- [propext, Classical.choice, Quot.sound]
```

Son los tres axiomas estándar sobre los que se apoya toda Mathlib. No hay `sorry` ni
supuestos adicionales.

## Ejercicios

1. (Papel) Construí explícitamente la dilatación de la matriz $3\times 3$ no
   uniestocástica del principio del capítulo. ¿Cuántas columnas de $U$ quedan
   determinadas por $\Gamma$ y cuántas son libres?
2. (Papel) Si $\Gamma$ ya es uniestocástica, con $\Gamma = |V|^2$, mostrá que existe una
   dilatación con un entorno de **una sola** configuración.
3. (Papel) En el instante $t = 0$, $\Gamma(0) = \mathbb{1}$. ¿Qué hace nuestra
   construcción con el entorno en ese instante? ¿Por qué eso impide tener
   $U(0) = \mathbb{1}$? ¿Cómo lo arreglarías?
4. (Lean, abierto) Fortalecé el teorema para que $U(0) = \mathbb{1}$. Es una tarea del
   roadmap.
