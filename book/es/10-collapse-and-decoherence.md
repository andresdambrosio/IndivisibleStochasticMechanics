# 10. Colapso y decoherencia como eventos de división

> Código: `IndivisibleStochasticMechanics/Quantum/Collapse.lean`,
> `IndivisibleStochasticMechanics/Quantum/Decoherence.lean`,
> `IndivisibleStochasticMechanics/Examples/MeasuredQubit.lean` y
> `IndivisibleStochasticMechanics/Examples/DecoheredQubit.lean`

## El problema

La mecánica cuántica de libro tiene **dos** leyes dinámicas:

1. Mientras nadie mira, el estado evoluciona de forma unitaria: $\psi \mapsto U\psi$.
2. Cuando alguien mide y obtiene el resultado $a$, el estado **colapsa** a $v_a$, y desde
   ahí sigue evolucionando con la primera ley.

La segunda ley es rara. No es unitaria ni lineal, y depende de una noción de "medición"
que la teoría nunca define. Muchos consideran que este es *el* problema de la mecánica
cuántica.

En el capítulo 9 vimos, siguiendo a Barandes ([Barandes, 2023a](https://arxiv.org/abs/2302.10778)), que la medición es una
interacción física más, y que las probabilidades de los resultados son las de Born. Ahora
damos el paso siguiente, que también es de Barandes. **El colapso no es una ley nueva, es
una consecuencia.** Y tiene
un significado estocástico preciso: la medición crea un **evento de división**.

## El modelo: evolucionar, medir, evolucionar

Usamos el mismo sistema y el mismo puntero que en el capítulo 9:

- el sistema empieza en la configuración $j$ y el puntero en reposo (*ready*);
- el sistema evoluciona con $U$ y el puntero queda quieto: $U \otimes \mathbb{1}$;
- una medición ideal $M$ del observable con autovectores $v_a$ (las columnas de $V$);
- el sistema sigue evolucionando con $W$ y el puntero, ya con el resultado registrado,
  queda quieto: $W \otimes \mathbb{1}$.

La evolución total del sistema compuesto es **una sola unitaria**:
$$\Theta = (W\otimes\mathbb{1})\,M\,(U\otimes\mathbb{1}).$$
No hay ninguna segunda ley. En Lean, esto es `measuredEvolution W M U`.

## La matemática

**Teorema (colapso).** Es un cálculo estándar del modelo de von Neumann; la versión formal
es nuestra. La amplitud de "sistema en $i$, puntero en $a$" es
$$\Theta_{(i,a),(j,\text{ready})} = (W v_a)_i \cdot \langle v_a|U|j\rangle .$$

*Demostración.* En el capítulo 9 vimos que, después de $M(U\otimes\mathbb 1)$, la
componente $(k, a)$ vale $(v_a)_k\,\langle v_a|U|j\rangle$. Como $W\otimes\mathbb 1$ no toca
el puntero, solo mezcla las configuraciones $k$ del sistema con el mismo $a$:
$$\Theta_{(i,a),(j,\text{ready})} = \sum_k W_{ik}\,(v_a)_k\,\langle v_a|U|j\rangle
= (Wv_a)_i\,\langle v_a|U|j\rangle. \qquad\blacksquare$$

Tomando el módulo al cuadrado:
$$P(i, a \mid j) = \underbrace{|\langle v_a|U|j\rangle|^2}_{\text{Born para } a}\;\cdot\;
\underbrace{|(W v_a)_i|^2}_{\text{evolucionar desde } v_a}.$$

Esta es exactamente la receta del libro de texto (von Neumann,
[1932](https://doi.org/10.1515/9781400889921)): se obtiene $a$ con la probabilidad de
Born y **después** el sistema evoluciona *como si* hubiera colapsado a $v_a$. Pero acá no
lo postulamos: es una identidad sobre la única evolución unitaria del sistema compuesto.
Lo que pasa después depende del pasado **solo a través del resultado registrado** $a$.

**Corolario (la medición borra la interferencia).** Si sumamos sobre el puntero, la matriz
de transición del sistema es
$$\Gamma_{\text{sis}} = |WV|^2 \cdot |V^\dagger U|^2,$$
donde $|A|^2$ es la matriz de módulos al cuadrado entrada por entrada. Sin medición, en
cambio, sería
$$|WU|^2 = \big|(WV)(V^\dagger U)\big|^2 .$$
La diferencia es justamente la interferencia. El módulo al cuadrado de un producto tiene
términos cruzados entre los distintos caminos $a$, y el producto de los módulos al
cuadrado no los tiene. La medición convierte "sumar amplitudes" en "sumar
probabilidades". Además, $|WV|^2$ y $|V^\dagger U|^2$ son las dos estocásticas, porque son
uniestocásticas: la evolución del sistema **se factoriza a través del resultado** $a$.

## El colapso como evento de división

Ahora lo decimos en el idioma del capítulo 4. Tomemos cualquier evolución unitaria $U(t)$
con $U(0) = \mathbb 1$ y medimos la **configuración** del sistema ($V = \mathbb 1$) en un
instante $t_1 > 0$. El sistema compuesto evoluciona así:

- para $t < t_1$: $U(t)\otimes\mathbb 1$;
- para $t \ge t_1$: $\big(U(t)U(t_1)^\dagger\otimes\mathbb 1\big)\,M\,\big(U(t_1)\otimes\mathbb 1\big)$.

Es decir, después de la medición el sistema sigue con **la misma dinámica** de antes. El
proceso del sistema, sumando sobre el puntero, es un proceso estocástico generalizado
(`GenStochasticProcess.measuredAt`).

**Teorema (colapso como evento de división).** El instante $t_1$ de la medición es un
evento de división de ese proceso, **cualquiera sea** la dinámica $U(t)$. La idea es de
Barandes ([2023a](https://arxiv.org/abs/2302.10778)); este enunciado formal y su
demostración en Lean son nuestros.

*Demostración.* Por el corolario, con $V = \mathbb 1$, para $t \ge t_1$ vale
$$\Gamma(t) = |U(t)U(t_1)^\dagger|^2 \cdot |U(t_1)|^2,
\qquad \Gamma(t_1) = |\mathbb 1|^2\cdot|U(t_1)|^2 = |U(t_1)|^2.$$
Entonces $\Gamma(t) = \Delta(t)\,\Gamma(t_1)$ con $\Delta(t) = |U(t)U(t_1)^\dagger|^2$, que
es estocástica. $\blacksquare$

### El qubit, otra vez

En el capítulo 6 demostramos que, para el qubit con $H = \sigma_x$, el instante $\pi/4$
**no** es un evento de división. A $\pi/4$ la distribución está completamente mezclada,
pero a $\pi/2$ el qubit intercambió sus configuraciones de forma determinista, y ninguna ley
estocástica puede recuperar esa información.

Si un aparato mide la configuración del qubit en $\pi/4$, la historia cambia (el ejemplo es
nuestro): $\pi/4$
**pasa a ser** un evento de división (`Qubit.measuredProcess_isDivisionEvent`). La misma
dinámica unitaria da una historia divisible o indivisible según haya o no una medición.

> Esta es la lectura de Barandes del colapso ([Barandes, 2023a](https://arxiv.org/abs/2302.10778)). Medir no cambia las leyes. Lo que hace es
> crear un evento de división: un instante a partir del cual podemos "reiniciar" el
> proceso y condicionar en lo que pasó, con probabilidades ordinarias.

## Decoherencia: nadie tiene que mirar

Releé la demostración del evento de división. En ningún momento usamos que alguien **lea**
el puntero. Lo único que importó es que el puntero quedó **correlacionado** con la
configuración del sistema. Entonces el aparato no tiene nada de especial: cualquier
entorno que registre la configuración debería producir lo mismo. Eso es la
**decoherencia** ([Zeh, 1970](https://doi.org/10.1007/BF00708656);
[Joos y Zeh, 1985](https://doi.org/10.1007/BF01725541);
[Zurek, 2003](https://arxiv.org/abs/quant-ph/0105127)), y ahora lo demostramos en general
en este modelo.

### El modelo

- Un **entorno** con cualquier espacio de configuraciones finito $m$, preparado en $e_0$.
  Puede ser un fotón, una molécula de aire o un aparato.
- Una interacción de **registro** $E$ que deja quieta la configuración del sistema y
  escribe un "registro" $\varphi_k$ en el entorno:
  $$E\big(|k\rangle\otimes|e_0\rangle\big) = |k\rangle\otimes|\varphi_k\rangle .$$
  Los $\varphi_k$ son vectores unitarios, pero **no hace falta que sean ortogonales**. El
  registro puede ser imperfecto: un fotón que rebota en un átomo puede llevarse solo un poco
  de información sobre dónde estaba.

**Teorema (existencia).** Para cualquier familia de registros unitarios $\varphi_k$ existe
una interacción unitaria $E$ que los produce. La demostración es el truco de siempre. Los
vectores $|k\rangle\otimes|\varphi_k\rangle$ son ortonormales aunque los $\varphi_k$ no lo sean,
porque la parte del sistema, $|k\rangle$, ya separa los distintos $k$. Después se completan a
una unitaria.

### La fórmula de la decoherencia

El sistema evoluciona con $U$, el entorno lo registra y después el sistema evoluciona con
$W$. Sumando sobre el entorno:

**Teorema (fórmula de la decoherencia).** Es la fórmula estándar de la teoría de la
decoherencia (ver [Schlosshauer, 2007](https://doi.org/10.1007/978-3-540-35775-9)), escrita
para probabilidades de transición.
$$\Gamma_{ij} = \sum_{k,l} W_{ik}U_{kj}\;\overline{W_{il}U_{lj}}\;\langle\varphi_l,\varphi_k\rangle .$$

Los términos con $k = l$ son probabilidades clásicas: ir de $j$ a $k$ y después de $k$ a
$i$. Los términos con $k \neq l$ son la interferencia entre los caminos que pasan por $k$ y
por $l$, y cada uno está **pesado por el solapamiento de sus registros**. Hay dos casos
extremos:

- **Registro perfecto** ($\varphi_k$ ortonormales): $\langle\varphi_l,\varphi_k\rangle = \delta_{kl}$ y
  $$\Gamma = |W|^2\cdot|U|^2 .$$
  La interferencia desaparece del todo.
- **Sin registro** (todos los $\varphi_k$ iguales): $\langle\varphi_l,\varphi_k\rangle = 1$ y
  $$\Gamma = |WU|^2 ,$$
  la evolución coherente, como si el entorno no estuviera.

Entre los dos extremos, la decoherencia apaga la interferencia en la medida exacta en que
el entorno distingue los caminos.

**Teorema (la decoherencia crea eventos de división).** La idea es de Barandes; el
enunciado formal y su demostración en Lean son nuestros. Si un entorno registra
perfectamente la configuración en $t_1$, entonces $t_1$ es un evento de división del
proceso del sistema, cualquiera sea la dinámica. **Nadie tiene que leer el registro.**

La medición del principio del capítulo es el caso particular en que el entorno es un
aparato.

### El qubit con un registro parcial

Volvamos al qubit con $H = \sigma_x$. En $\pi/4$, un qubit del entorno registra su
configuración de forma imperfecta: la configuración $0$ deja el registro $(1, 0)$ y la $1$
deja $(\cos\theta, \sin\theta)$. El solapamiento es $\cos\theta$. Con $\theta = \pi/2$ el
registro es perfecto, y con $\theta = 0$ no hay registro.

**Teorema.** La probabilidad de que el qubit haya intercambiado su configuración en
$\pi/2$ es
$$P(\text{intercambio}) = \frac{1 + \cos\theta}{2} .$$

Sin registro ($\cos\theta = 1$) da $1$: el intercambio determinista del capítulo 6. Con
registro perfecto ($\cos\theta = 0$) da $1/2$: la interferencia se borró y queda una moneda.
En el medio, la curva es continua.

**Teorema.** $\pi/4$ es un evento de división **si y solo si** el registro es perfecto,
$\cos\theta = 0$.

Este ejemplo y sus dos teoremas son nuestros. Hasta donde sabemos, este enunciado preciso
no aparece en la literatura.

Que un registro parcial no alcance es importante. Un evento de división no es "un poco"
verdadero: o la dinámica se factoriza o no. En el mundo real los registros nunca son
perfectos, pero se vuelven perfectos muy rápido: muchos fotones, cada uno con un
solapamiento cercano a uno, multiplican sus solapamientos, que se van a cero en forma
exponencial ([Joos y Zeh, 1985](https://doi.org/10.1007/BF01725541)). Barandes, Hasan y
Kagan dicen explícitamente que los eventos de división "a menudo son solo aproximados o
efectivos", válidos hasta "cierto nivel de precisión" ([Barandes, Hasan y Kagan, 2025](https://arxiv.org/abs/2512.18105), §3.1), pero no dan una
medida de esa precisión. Definirla, y formalizarla, es una de las tareas siguientes.

## Lo que todavía falta

- **Observables arbitrarios.** El teorema del evento de división vale para mediciones de
  la configuración ($V = \mathbb 1$). Para $V$ general, $\Gamma_{\text{sis}}(t_1) =
  |V|^2|V^\dagger U|^2$ y la factorización no es inmediata. El enunciado natural es sobre el
  proceso compuesto sistema + puntero.
- **Mediciones repetidas** y el efecto Zeno cuántico.
- **Decoherencia continua.** Registros que se acumulan en el tiempo, y una noción
  cuantitativa de "casi divisible" para registros casi perfectos.

## En Lean

```lean
def measuredEvolution (W : Matrix n n ℂ) (M : Matrix (n × Option n) (n × Option n) ℂ)
    (U : Matrix n n ℂ) : Matrix (n × Option n) (n × Option n) ℂ :=
  (W ⊗ₖ (1 : Matrix (Option n) (Option n) ℂ)) *
    (M * (U ⊗ₖ (1 : Matrix (Option n) (Option n) ℂ)))

theorem IsIdealMeasurement.collapse_apply (hM : IsIdealMeasurement V M) (i j a : n) :
    measuredEvolution W M U (i, some a) (j, none) = (W * V) i a * (Vᴴ * U) a j

theorem IsIdealMeasurement.pointerMarginal_measuredEvolution (hM : IsIdealMeasurement V M) :
    pointerMarginal (measuredEvolution W M U) =
      normSqMatrix (W * V) * normSqMatrix (Vᴴ * U)

theorem GenStochasticProcess.measuredAt_isDivisionEvent (hMV : IsIdealMeasurement 1 M) :
    (measuredAt U hU h0 M hM t₁ ht₁).IsDivisionEvent t₁
```

```lean
def IsRecording (φ : n → m → ℂ) (E : Matrix (n × m) (n × m) ℂ) (e₀ : m) : Prop :=
  E ∈ unitaryGroup (n × m) ℂ ∧ ∀ i e j, E (i, e) (j, e₀) = if i = j then φ j e else 0

theorem IsRecording.envMarginal_recordedEvolution (hE : IsRecording φ E e₀)
    (W U : Matrix n n ℂ) (i j : n) :
    (envMarginal (recordedEvolution W E U) e₀ i j : ℂ) =
      ∑ k, ∑ l, W i k * U k j * star (W i l * U l j) * overlap φ k l

theorem Qubit.decoheredProcess_isDivisionEvent_iff (θ : ℝ) :
    (decoheredProcess θ).IsDivisionEvent (Real.pi / 4) ↔ Real.cos θ = 0
```

`(W * V) i a` es $(W v_a)_i$ y `(Vᴴ * U) a j` es $\langle v_a|U|j\rangle$. Fijate que
`collapse_apply` ni siquiera necesita que $V$ sea unitaria: es pura álgebra. La unitariedad
aparece recién cuando queremos que las probabilidades sumen uno.

## Ejercicios

1. (Papel) Para el qubit medido en $\pi/4$, calculá $\Gamma(\pi/2)$ y comparala con la del
   qubit sin medir. ¿Qué información se perdió?
2. (Papel) Mostrá con un ejemplo de $2\times 2$ que $|AB|^2 \neq |A|^2|B|^2$ en general, e
   identificá el término de interferencia.
3. (Para pensar) En el modelo, el puntero queda quieto después de la medición. ¿Qué
   pasaría con el evento de división si el puntero también evolucionara?
4. (Papel) Con la fórmula de la decoherencia, calculá $P(\text{intercambio})$ para el qubit
   con un registro de solapamiento complejo $\lambda$. ¿Qué parte de $\lambda$ importa?
5. (Para pensar) $N$ fotones, cada uno con solapamiento $\lambda$, dejan un registro total
   con solapamiento $\lambda^N$. ¿Cuántos fotones hacen falta para que $P(\text{intercambio})$
   difiera de $1/2$ en menos de $10^{-6}$ si $\lambda = 0{,}99$?
6. (Lean, abierto) Demostrá que medir el qubit dos veces, en $t_1 < t_2$, crea dos eventos
   de división.
