# 11. Sistemas compuestos y entrelazamiento

> Código: `IndivisibleStochasticMechanics/Quantum/Composite.lean`,
> `IndivisibleStochasticMechanics/Quantum/Bell.lean`,
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
aparece el entrelazamiento en un ejemplo concreto. Al final verificamos el teorema de Bell
en su forma CHSH y la cota de Tsirelson.

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
[Barandes, 2024](https://arxiv.org/abs/2402.16935).

**Teorema (no señalización para cualquier operación local).** Ahora Bob hace cualquier cosa
de su lado: trae su propio sistema auxiliar $E$ (por ejemplo el puntero de un aparato) en
un estado $e_0$, y aplica cualquier unitaria $N$ a su sistema junto con $E$. Las
probabilidades de transición de Alicia no cambian:
$$\sum_{i_2,\,e}\Big|\big(N_{\text{Bob}}\,(\Theta\otimes\mathbb 1)\big)_{((i_1,i_2),e),\,(j,e_0)}\Big|^2
= \sum_{i_2}\big|\Theta_{(i_1,i_2),j}\big|^2 .$$
*Demostración:* para $i_1$ y $j$ fijos, el lado izquierdo es la norma al cuadrado de $N x$
con $x_{(i_2,e)} = \Theta_{(i_1,i_2),j}\,\delta_{e,e_0}$, y $N$ preserva la norma.
$\blacksquare$ En particular, **que Bob mida su sistema con su propio aparato** (ideal como en
el capítulo 9, o no) no se ve en las estadísticas de Alicia. Toda operación cuántica local
se puede escribir así, con un sistema auxiliar (teorema de Stinespring, ver el capítulo 8 y las [referencias](99-references.md)), así
que esto las cubre a todas. El enunciado formal es nuestro; el resultado es de Ghirardi,
Rimini y Weber.

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

## No localidad de Bell: CHSH y Tsirelson

El par de Bell también nos deja verificar en Lean el teorema más famoso sobre el
entrelazamiento. Alicia elige una de dos configuraciones del aparato, $x\in\{0,1\}$, y Bob
una de dos, $y\in\{0,1\}$. Cada uno obtiene un resultado $\pm1$, y $E(x,y)$ es el promedio
del producto de los resultados. La **combinación CHSH** es
$$S = E(0,0) + E(0,1) + E(1,0) - E(1,1).$$

**Teorema (desigualdad CHSH).** En todo modelo de variables ocultas locales, $|S|\le 2$.

Un *modelo de variables ocultas locales* es el tipo de teoría que consideró Bell
([Bell, 1964](https://doi.org/10.1103/PhysicsPhysiqueFizika.1.195)): una variable oculta
$\lambda$ se sortea con alguna distribución, y el resultado de Alicia depende solo de
$\lambda$ y de su elección, no de la de Bob (y al revés). La desigualdad es la de
[Clauser, Horne, Shimony y Holt, 1969](https://doi.org/10.1103/PhysRevLett.23.880).
*Demostración:* para cada $\lambda$, con $a_x, b_y\in[-1,1]$, el número
$a_0(b_0+b_1) + a_1(b_0-b_1)$ tiene valor absoluto a lo sumo $|b_0+b_1| + |b_0-b_1| \le 2$;
promediar sobre $\lambda$ conserva la cota. $\blacksquare$ En Lean tomamos $\lambda$ en un
conjunto finito y resultados en $[-1,1]$, lo que cubre también el azar local.

**Teorema (el par de Bell, en lenguaje estocástico).** Alicia rota su qubit un ángulo $a$ y
Bob rota el suyo un ángulo $b$ (unitarias locales), y después se leen las dos
configuraciones. Con resultado $+1$ para la configuración $0$ y $-1$ para la $1$, las
probabilidades de transición del proceso compuesto dan
$$E(a,b) = \cos 2(a-b).$$
Con los ángulos estándar $a\in\{0,\pi/4\}$ y $b\in\{\pi/8,-\pi/8\}$,
$$S = 2\sqrt2 \approx 2{,}83 > 2.$$
Entonces **ningún modelo de variables ocultas locales reproduce estas probabilidades de
transición.** La cuenta es mecánica cuántica de libro; enunciarla para las probabilidades
de transición del proceso compuesto es nuestro (para el juego CHSH en este marco, ver
también [Barandes, Hasan y Kagan, 2025](https://arxiv.org/abs/2512.18105)).

**Teorema (cota de Tsirelson).** Para cualquier estado $\psi$ y observables
$A_0, A_1, B_0, B_1$ con autovalores $\pm1$, donde los de Alicia conmutan con los de Bob,
$$\langle\psi, (A_0B_0 + A_0B_1 + A_1B_0 - A_1B_1)\,\psi\rangle \le 2\sqrt2\,\|\psi\|^2 .$$
Es el resultado de [Cirel'son, 1980](https://doi.org/10.1007/BF00417500). *Demostración*
(el argumento estándar de suma de cuadrados): con $s = \sqrt2$,
$$(sA_0 - B_0 - B_1)^2 + (sA_1 - B_0 + B_1)^2 = 8 - 2s\,(A_0B_0 + A_0B_1 + A_1B_0 - A_1B_1),$$
y el lado izquierdo tiene valor esperado no negativo. $\blacksquare$ Así que el par de Bell
es óptimo: la mecánica cuántica supera 2, pero nunca $2\sqrt2$.

**Teorema (Tsirelson, en lenguaje estocástico).** La misma cota vale directamente para las
probabilidades de transición de un proceso compuesto. Tomá cualquier preparación unitaria
$\Theta$ de los dos sistemas, cualesquiera unitarias locales $U_x$ para Alicia y $V_y$ para
Bob, y cualquier asignación de resultados $\pm1$ a las configuraciones. Entonces las
correlaciones
$$E(x,y) = \sum_{i_1,i_2} a_x(i_1)\,b_y(i_2)\;\Gamma^{xy}_{(i_1,i_2),\,j}$$
calculadas con las matrices de transición $\Gamma^{xy}$ cumplen $|S| \le 2\sqrt2$.
*Demostración:* $E(x,y)$ es el valor esperado cuántico de
$(U_x^\dagger D_{a_x} U_x)\otimes(V_y^\dagger D_{b_y} V_y)$ en el estado $\Theta e_j$, donde
$D_a$ es la matriz diagonal de resultados. Esos observables tienen cuadrado $1$, así que
vale el teorema anterior. $\blacksquare$ La cota es de Cirel'son. Barandes, Hasan y Kagan
derivan la cota de Tsirelson dentro de la mecánica estocástica indivisible, para procesos
uniestocásticos y a partir del principio de localidad causal ([Barandes, Hasan y Kagan, 2025](https://arxiv.org/abs/2512.18105)). Nuestro enunciado
es una versión distinta y más directa: para las probabilidades de transición mismas, con
unitarias locales. Esa versión y su demostración formal son nuestras.

**Teorema (con aparatos).** Hasta acá, "medir" quería decir rotar y después leer la
configuración. Ahora cada lado mide con un aparato ideal como el del capítulo 9: Alicia con
un aparato para la base $V_x$ y su propio puntero, Bob con uno para $W_y$ y su propio
puntero. Cada aparato actúa solo sobre su sistema y su puntero. Entonces los punteros
marcan $(a,b)$ con probabilidad
$$P(a,b) = \Big|\big((V_x^\dagger\otimes W_y^\dagger)\,\Theta\big)_{(a,b),\,j}\Big|^2 ,$$
que es exactamente la probabilidad de "rotar con $V_x^\dagger$, $W_y^\dagger$ y leer".
En consecuencia, **los punteros también cumplen $|S|\le 2\sqrt2$**, y para el par de Bell,
con aparatos para las bases rotadas, **los punteros llegan a $S = 2\sqrt2$**. La física es
la teoría de la medición estándar; estos tres enunciados en esta forma, y sus
demostraciones formales, son nuestros.

¿Qué significa esto para la mecánica estocástica indivisible? Las configuraciones son
reales en todo instante, pero **no** son una variable oculta local en el sentido de Bell:
el teorema muestra que ninguna variable así reproduce las estadísticas. En el lenguaje de
este libro, la razón es la que ya vimos: el instante justo después de la preparación no es
un evento de división, así que la configuración en ese instante no "aísla" el futuro. Esta
lectura es nuestra; para cómo encaja la localidad en la formulación de Barandes, ver
[Barandes, 2024](https://arxiv.org/abs/2402.16935) y, para CHSH en particular, [Barandes, Hasan y Kagan, 2025](https://arxiv.org/abs/2512.18105).

## Lo que todavía falta

- **Mediciones no ideales.** Los aparatos de acá son ideales (proyectivos). Las mediciones
  generales (POVM) quedan pendientes.
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

```lean
theorem LHVModel.abs_chsh_corr_le_two (L : LHVModel Λ) : |chsh L.corr| ≤ 2

theorem BellPair.corr_eq (a b : ℝ) : corr a b = Real.cos (2 * (a - b))
theorem BellPair.chsh_bellCorr : chsh bellCorr = 2 * Real.sqrt 2
theorem BellPair.lhv_corr_ne_bellCorr (L : LHVModel Λ) : L.corr ≠ bellCorr

theorem expect_chsh_le ... (ψ : ι → ℂ) :
    expect (A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁) ψ ≤ 2 * Real.sqrt 2 * ∑ i, ‖ψ i‖ ^ 2

theorem abs_chsh_stochCorr_le (hΘ : Θ ∈ unitaryGroup (A × B) ℂ) (hU : ∀ x, U x ∈ ...)
    (hV : ∀ y, V y ∈ ...) (ha : ∀ x i, a x i = 1 ∨ a x i = -1) (hb : ...) (j : A × B) :
    |chsh (stochCorr Θ U V a b j)| ≤ 2 * Real.sqrt 2

theorem pointerJoint_eq (hM : IsIdealMeasurement V M) (hN : IsIdealMeasurement W N)
    (hV : V ∈ unitaryGroup A ℂ) (hW : W ∈ unitaryGroup B ℂ) (Θ) (j) (a) (b) :
    pointerJoint M N Θ j a b = normSqMatrix ((Vᴴ ⊗ₖ Wᴴ) * Θ) (a, b) j

theorem BellPair.chsh_pointerCorr (hM : ∀ x, IsIdealMeasurement (rot (alice x))ᴴ (M x))
    (hN : ∀ y, IsIdealMeasurement (rot (bob y))ᴴ (N y)) :
    chsh (pointerCorr M N prep (fun _ => sgn) (fun _ => sgn) (0, 0)) = 2 * Real.sqrt 2
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
5. (Papel) Verificá que $S = 2\sqrt2$ a partir de $E(a,b) = \cos 2(a-b)$ y los cuatro ángulos.
6. (Papel) ¿Por qué la demostración de no señalización necesita que el sistema auxiliar
   sea solo de Bob? ¿Qué falla si lo comparte con Alicia?
