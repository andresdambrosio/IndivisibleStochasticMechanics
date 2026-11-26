# 11. Sistemas compuestos y entrelazamiento

> Código: `IndivisibleStochasticMechanics/Quantum/Composite.lean`,
> `IndivisibleStochasticMechanics/Examples/BellPair.lean` y
> `IndivisibleStochasticMechanics/ForMathlib/Matrix/Stochastic.lean`

## La idea física

Dos sistemas, con espacios de configuraciones $\mathcal{C}_1$ y $\mathcal{C}_2$, forman un
sistema compuesto cuyas configuraciones son **pares** $(i_1, i_2)$. No hace falta nada
más: en la mecánica estocástica indivisible, un sistema compuesto es simplemente un
sistema cuyo espacio de configuraciones es un producto cartesiano. Barandes trata los
sistemas compuestos y el entrelazamiento en
[Barandes, 2023a, §3.9](https://arxiv.org/abs/2302.10778).

En la mecánica cuántica de libro, el **entrelazamiento** es lo más misterioso de los
sistemas compuestos. Lo señalaron Einstein, Podolsky y Rosen
([1935](https://doi.org/10.1103/PhysRev.47.777)), y Schrödinger le puso nombre
(*Verschränkung*) ese mismo año ([Schrödinger, 1935](https://doi.org/10.1007/BF01491891)).
En este capítulo vemos tres cosas en lenguaje estocástico: qué pasa cuando los sistemas
no interactúan, por qué lo que hace uno no se ve en las estadísticas del otro, y cómo
aparece el entrelazamiento en un ejemplo concreto.

## Sistemas independientes

Si los dos sistemas no interactúan nunca, cada uno evoluciona con su propia unitaria y el
compuesto evoluciona con el producto de Kronecker $U(t)\otimes V(t)$. Como
$$|(A\otimes B)_{(i_1,i_2),(j_1,j_2)}|^2 = |A_{i_1j_1}|^2\,|B_{i_2j_2}|^2 ,$$
la regla de Born da

**Teorema (sistemas independientes).** El proceso del compuesto es el producto de
Kronecker de los procesos:
$$\Gamma(t) = \Gamma_1(t)\otimes\Gamma_2(t).$$

Para que eso tenga sentido hace falta un lema de álgebra lineal: **el producto de Kronecker
de dos matrices estocásticas es estocástico**. La columna $(j_1, j_2)$ suma
$\sum_{i_1}\Gamma^{(1)}_{i_1j_1}\cdot\sum_{i_2}\Gamma^{(2)}_{i_2j_2} = 1\cdot 1$. El lema
es general y no estaba en Mathlib, así que lo pusimos en `ForMathlib/`.

**Teorema.** Si $t'$ es un evento de división de los dos procesos, también lo es del
producto. *Demostración:* si $\Gamma_1(t) = \Delta_1(t)\Gamma_1(t')$ y
$\Gamma_2(t) = \Delta_2(t)\Gamma_2(t')$, la propiedad
$(A B)\otimes(C D) = (A\otimes C)(B\otimes D)$ da
$\Gamma(t) = \big(\Delta_1(t)\otimes\Delta_2(t)\big)\,\Gamma(t')$. $\blacksquare$

Estos resultados son estándar; los enunciados formales son nuestros.

## No señalización

Ahora los sistemas sí pueden haber interactuado: la evolución conjunta $\Theta$ es
cualquier cosa. Alicia tiene el sistema 1 y Bob el sistema 2. Bob aplica una operación
unitaria $B$ solo a su sistema. ¿Puede Alicia notarlo?

**Teorema (no señalización).** Para cualquier evolución conjunta $\Theta$ y cualquier
unitaria $B$ sobre el sistema 2, las probabilidades de transición del sistema 1 no cambian:
$$\sum_{i_2}\Big|\big((\mathbb 1\otimes B)\,\Theta\big)_{(i_1,i_2),(j_1,j_2)}\Big|^2
= \sum_{i_2}\big|\Theta_{(i_1,i_2),(j_1,j_2)}\big|^2 .$$

*Demostración.* Para $i_1$, $j_1$ y $j_2$ fijos, el lado izquierdo es la norma al cuadrado
del vector $B x$, con $x_{i_2} = \Theta_{(i_1,i_2),(j_1,j_2)}$. Una unitaria preserva la
norma. $\blacksquare$

Es la versión estocástica del teorema de no señalización de la mecánica cuántica
([Ghirardi, Rimini y Weber, 1980](https://doi.org/10.1007/BF02817189)): lo que hace Bob no
aparece en las estadísticas de Alicia, así que no sirve para mandar mensajes. Barandes
discute la localidad causal de su formulación en
[Barandes, 2024](https://arxiv.org/abs/2402.16935). Por ahora formalizamos solo el caso de
operaciones unitarias; el caso de mediciones locales queda pendiente.

## Entrelazamiento: un par de Bell

Dos qubits empiezan en la configuración $(0,0)$. Una compuerta de Hadamard
$H = \tfrac{1}{\sqrt 2}\begin{pmatrix}1&1\\1&-1\end{pmatrix}$ sobre el primero y una CNOT
($|a,b\rangle\mapsto|a, b\oplus a\rangle$) preparan el estado de Bell
$$\frac{|00\rangle + |11\rangle}{\sqrt 2}$$
(ver por ejemplo [Nielsen y Chuang, 2000, §1.3.6](https://doi.org/10.1017/CBO9780511976667)).
Este ejemplo y sus cuatro teoremas en lenguaje estocástico son nuestros. Los hechos
cuánticos que usan son de libro.

**Teorema (correlación).** Justo después de la preparación, los dos qubits coinciden: la
configuración es $(0,0)$ o $(1,1)$, cada una con probabilidad $1/2$. Esta distribución
**no es un producto** $p\otimes q$.

*Demostración del segundo punto.* Si lo fuera, $p_0 q_0 = 1/2$, $p_1 q_1 = 1/2$ y
$p_0 q_1 = 0$. Pero de $p_0 q_1 = 0$ sale $p_0 = 0$ o $q_1 = 0$, y cualquiera de las dos
contradice una de las otras igualdades. $\blacksquare$

Hasta acá no hay nada cuántico: dos monedas que alguien pegó juntas también coinciden
siempre. La diferencia aparece cuando cambiamos de base.

**Teorema (sin evento de división).** Si después de la preparación aplicamos un Hadamard a
**cada** qubit, los qubits *siguen* coincidiendo con certeza: $(0,0)$ o $(1,1)$, cada una con
probabilidad $1/2$. Es porque el estado de Bell es invariante bajo $H\otimes H$.

**Teorema (con evento de división).** Si justo después de la preparación un entorno
**registra** la configuración de los dos qubits (un registro perfecto, como en el
capítulo 10), los mismos Hadamards locales dan la distribución **uniforme**: cada una de
las cuatro configuraciones con probabilidad $1/4$. Nadie tiene que leer el registro.

En el instante intermedio, las dos historias tienen **exactamente las mismas**
estadísticas de configuraciones: $(0,0)$ o $(1,1)$ con probabilidad $1/2$. Lo que las
distingue es si ese instante es o no un evento de división.

> En el lenguaje de este libro, el entrelazamiento del par de Bell se ve así:
> **correlaciones más la ausencia de un evento de división**. Las monedas pegadas son
> correlaciones *con* un evento de división. Esta es nuestra forma de resumir el ejemplo;
> para la discusión general de Barandes ver
> [Barandes, 2023a, §3.9](https://arxiv.org/abs/2302.10778).

## Lo que todavía falta

- **Bell y CHSH.** El paso siguiente es mostrar que ninguna teoría de variables ocultas
  locales reproduce estas correlaciones ([Bell, 1964](https://doi.org/10.1103/PhysicsPhysiqueFizika.1.195);
  [Clauser, Horne, Shimony y Holt, 1969](https://doi.org/10.1103/PhysRevLett.23.880)), y
  que el valor cuántico de CHSH está acotado por $2\sqrt 2$
  ([Cirel'son, 1980](https://doi.org/10.1007/BF00417500)). En nuestro lenguaje, eso
  requiere medir con aparatos (capítulo 9) observables que no conmutan sobre cada qubit.
- **No señalización para mediciones locales**, no solo para unitarias.
- **La pregunta de la localidad.** Barandes sostiene que su formulación es causalmente
  local ([Barandes, 2024](https://arxiv.org/abs/2402.16935)). Formalizar ese enunciado es
  una tarea de la etapa III del roadmap.

## En Lean

```lean
theorem Matrix.kronecker_mem_colStochastic (hA : A ∈ colStochastic R m)
    (hB : B ∈ colStochastic R n) : A ⊗ₖ B ∈ colStochastic R (m × n)

def GenStochasticProcess.prod (P : GenStochasticProcess n) (Q : GenStochasticProcess m) :
    GenStochasticProcess (n × m) where
  Γ t := P.Γ t ⊗ₖ Q.Γ t
  ...

theorem GenStochasticProcess.prod_isDivisionEvent (hP : P.IsDivisionEvent t')
    (hQ : Q.IsDivisionEvent t') : (P.prod Q).IsDivisionEvent t'

theorem envMarginal_one_kronecker_mul (hB : B ∈ unitaryGroup m ℂ)
    (Θ : Matrix (n × m) (n × m) ℂ) (e₀ : m) :
    envMarginal (((1 : Matrix n n ℂ) ⊗ₖ B) * Θ) e₀ = envMarginal Θ e₀
```

`envMarginal Θ e₀` es la matriz de transición del sistema 1 sumando sobre el sistema 2,
con el sistema 2 empezando en $e_0$: la misma que usamos para el entorno en el capítulo 10.
Acá el "entorno" es el sistema de Bob.

```lean
theorem BellPair.not_product :
    ¬ ∃ p q : Fin 2 → ℝ, ∀ i, normSqMatrix prep i (0, 0) = p i.1 * q i.2

theorem BellPair.coherent (i : Fin 2 × Fin 2) :
    normSqMatrix ((hadamard ⊗ₖ hadamard) * prep) i (0, 0) = if i.1 = i.2 then 1 / 2 else 0

theorem BellPair.decohered_of_isRecording (hE : IsRecording φ E e₀)
    (hφ : ∀ k l, overlap φ k l = if k = l then 1 else 0) (i : Fin 2 × Fin 2) :
    envMarginal (recordedEvolution (hadamard ⊗ₖ hadamard) E prep) e₀ i (0, 0) = 1 / 4
```

## Ejercicios

1. (Papel) Verificá a mano que $(H\otimes H)\,\tfrac{1}{\sqrt2}(|00\rangle+|11\rangle) =
   \tfrac{1}{\sqrt2}(|00\rangle+|11\rangle)$.
2. (Papel) En el par de Bell, ¿cuál es la distribución de las configuraciones del qubit de
   Alicia sola? ¿Cambia si Bob aplica un Hadamard? Compará con el teorema de no
   señalización.
3. (Papel) Repetí el ejemplo con el estado $\tfrac{1}{\sqrt2}(|01\rangle-|10\rangle)$. ¿Qué
   compuertas locales dejan las correlaciones intactas?
4. (Para pensar) Las "monedas pegadas" y el par de Bell tienen la misma distribución en el
   instante intermedio. ¿Hay alguna forma de distinguirlos mirando solo ese instante?
5. (Lean, abierto) Extendé el teorema de no señalización a una medición ideal hecha por Bob
   sobre su qubit.
