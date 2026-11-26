# 1. Por qué reformular la mecánica cuántica

## La teoría que funciona y que nadie entiende

La mecánica cuántica es la teoría física con más éxito predictivo de la historia. Sin
embargo, su formulación de libro de texto, la de Dirac (1930) y von
Neumann ([1932](https://doi.org/10.1515/9781400889921)), tiene una estructura incómoda:

1. El estado de un sistema es un vector $|\psi\rangle$ en un espacio de Hilbert.
2. Mientras nadie mide, $|\psi\rangle$ evoluciona de forma determinista y unitaria:
   $|\psi(t)\rangle = U(t)|\psi(0)\rangle$.
3. Cuando alguien *mide*, el estado "colapsa" de forma aleatoria, con probabilidades dadas
   por la **regla de Born** ([Born, 1926](https://doi.org/10.1007/BF01397477)):
   $P(i) = |\langle i|\psi\rangle|^2$.

Esta estructura genera el famoso **problema de la medición**. ¿Qué cuenta como una
medición? ¿Por qué hay dos leyes de evolución distintas? ¿Qué *es* $|\psi\rangle$:
algo físico, o un registro de nuestro conocimiento? Las distintas interpretaciones
(Copenhague, muchos mundos, Bohm, colapso objetivo, QBismo...) son respuestas diferentes
a estas preguntas.

## La propuesta de Barandes

Barandes ([Barandes, 2023a](https://arxiv.org/abs/2302.10778), [Barandes, 2025](https://arxiv.org/abs/2507.21192)) propone darle la vuelta al orden habitual. En
nuestras palabras:

> Un sistema cuántico **es** un sistema que, en cada instante, está en una configuración
> definida (una de las posibles $i \in \mathcal{C}$), y que salta entre configuraciones
> de forma aleatoria siguiendo leyes probabilísticas *ordinarias*.

Lo que no es ordinario es el tipo de ley. En un proceso de Markov, la probabilidad de
ir de $j$ en el instante $0$ a $i$ en el instante $t$ se puede descomponer pasando por
cualquier instante intermedio $t'$:

$$\Gamma(t \leftarrow 0) = \Gamma(t \leftarrow t')\,\Gamma(t' \leftarrow 0).$$

Barandes trabaja con procesos en los que esta descomposición **no** existe en general.
A esos procesos los llama **indivisibles**. Las leyes solo dicen cómo se condiciona
respecto del instante inicial, y no paso a paso.

El resultado central de Barandes, la **correspondencia estocástico-cuántica**
([Barandes, 2023a](https://arxiv.org/abs/2302.10778), [Barandes, 2023b](https://arxiv.org/abs/2309.03085)), dice lo siguiente:

- Toda evolución cuántica unitaria define un proceso indivisible, mediante
  $\Gamma_{ij}(t) = |U_{ij}(t)|^2$.
- Todo proceso indivisible se puede representar en un espacio de Hilbert, con una
  evolución unitaria en un espacio de configuraciones posiblemente más grande.

Por tanto, **las dos descripciones son equivalentes**. Según Barandes, en la versión
estocástica:

- La función de onda deja de ser un objeto físico y pasa a ser una herramienta de
  cálculo.
- No hay colapso como proceso físico: medir es actualizar probabilidades ordinarias.
- La interferencia, el entrelazamiento y los observables que no conmutan **aparecen solos**
  a partir de la indivisibilidad.

## Qué aporta formalizar

Esta sección es la motivación de este proyecto, no de Barandes.

La correspondencia es una afirmación matemática precisa, y por eso se puede verificar.
Hay tres razones para hacerlo en Lean:

1. **Rigor.** En fundamentos de la física es fácil deslizar supuestos sin darse cuenta.
   Lean obliga a escribir cada hipótesis.
2. **Colaboración.** Si un teorema compila, es correcto, sin importar quién lo escribió.
   Esto permite que contribuya gente desconocida y no hay que confiar en nadie.
3. **Extensión.** Para llevar la teoría más allá (espacios continuos, campos,
   relatividad), hace falta una base sólida. Cada resultado nuevo se apoya en los
   anteriores, que ya están verificados.

## Lo que esta teoría no es (todavía)

Conviene ser honestos. El propio Barandes presenta su formulación como empíricamente
equivalente a la mecánica cuántica: tal como está formulada, la mecánica estocástica
indivisible **hace las mismas predicciones** que la mecánica cuántica. Por eso, "reemplazar" la
mecánica cuántica significa hoy reemplazar su *ontología*, es decir, qué existe según la
teoría, y no sus predicciones. Si hay física nueva, aparecerá al explorar los bordes:
qué procesos son físicamente admisibles, qué pasa con las estadísticas en varios
instantes, cómo se lleva la teoría con la relatividad. De eso trata la Parte IV.

## Lecturas

- J. A. Barandes, *The Stochastic-Quantum Correspondence*,
  [arXiv:2302.10778](https://arxiv.org/abs/2302.10778); Philosophy of Physics 3(1): 8
  (2025). Es el texto base.
- J. A. Barandes, *Quantum Systems as Indivisible Stochastic Processes*,
  [arXiv:2507.21192](https://arxiv.org/abs/2507.21192); Stud. Hist. Phil. Sci. 119,
  102213 (2026). Es una versión más corta y conceptual.
- J. A. Barandes, *The Stochastic-Quantum Theorem*,
  [arXiv:2309.03085](https://arxiv.org/abs/2309.03085). Contiene el teorema en detalle.
