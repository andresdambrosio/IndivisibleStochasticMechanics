# 10. Colapso y decoherencia como eventos de división

> Código: `IndivisibleStochasticMechanics/Quantum/Collapse.lean` y
> `IndivisibleStochasticMechanics/Examples/MeasuredQubit.lean`

## El problema

La mecánica cuántica de libro tiene **dos** leyes dinámicas:

1. Mientras nadie mira, el estado evoluciona de forma unitaria: $\psi \mapsto U\psi$.
2. Cuando alguien mide y obtiene el resultado $a$, el estado **colapsa** a $v_a$, y desde
   ahí sigue evolucionando con la primera ley.

La segunda ley es rara. No es unitaria ni lineal, y depende de una noción de "medición"
que la teoría nunca define. Muchos consideran que este es *el* problema de la mecánica
cuántica.

En el capítulo 9 vimos que en la mecánica estocástica indivisible la medición es una
interacción física más, y que las probabilidades de los resultados son las de Born. Ahora
damos el paso siguiente. **El colapso no es una ley nueva, es una consecuencia.** Y tiene
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

**Teorema (colapso).** La amplitud de "sistema en $i$, puntero en $a$" es
$$\Theta_{(i,a),(j,\text{ready})} = (W v_a)_i \cdot \langle v_a|U|j\rangle .$$

*Demostración.* En el capítulo 9 vimos que, después de $M(U\otimes\mathbb 1)$, la
componente $(k, a)$ vale $(v_a)_k\,\langle v_a|U|j\rangle$. Como $W\otimes\mathbb 1$ no toca
el puntero, solo mezcla las configuraciones $k$ del sistema con el mismo $a$:
$$\Theta_{(i,a),(j,\text{ready})} = \sum_k W_{ik}\,(v_a)_k\,\langle v_a|U|j\rangle
= (Wv_a)_i\,\langle v_a|U|j\rangle. \qquad\blacksquare$$

Tomando el módulo al cuadrado:
$$P(i, a \mid j) = \underbrace{|\langle v_a|U|j\rangle|^2}_{\text{Born para } a}\;\cdot\;
\underbrace{|(W v_a)_i|^2}_{\text{evolucionar desde } v_a}.$$

Esta es exactamente la receta del libro de texto: se obtiene $a$ con la probabilidad de
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
unistocásticas: la evolución del sistema **se factoriza a través del resultado** $a$.

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
evento de división de ese proceso, **cualquiera sea** la dinámica $U(t)$.

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

Si un aparato mide la configuración del qubit en $\pi/4$, la historia cambia: $\pi/4$
**pasa a ser** un evento de división (`Qubit.measuredProcess_isDivisionEvent`). La misma
dinámica unitaria da una historia divisible o indivisible según haya o no una medición.

> Esta es la lectura de Barandes del colapso. Medir no cambia las leyes. Lo que hace es
> crear un evento de división: un instante a partir del cual podemos "reiniciar" el
> proceso y condicionar en lo que pasó, con probabilidades ordinarias.

## Lo que todavía falta

- **Observables arbitrarios.** El teorema del evento de división vale para mediciones de
  la configuración ($V = \mathbb 1$). Para $V$ general, $\Gamma_{\text{sis}}(t_1) =
  |V|^2|V^\dagger U|^2$ y la factorización no es inmediata. El enunciado natural es sobre el
  proceso compuesto sistema + puntero.
- **Mediciones repetidas** y el efecto Zeno cuántico.
- **Decoherencia.** Un aparato es un caso especial de un *entorno* que registra la
  configuración. Queremos demostrar que cualquier entorno que registra crea eventos de
  división, aunque nadie "lea" el registro. Esta sección del capítulo se va a completar
  cuando esté el código.

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
4. (Lean, abierto) Demostrá que medir el qubit dos veces, en $t_1 < t_2$, crea dos eventos
   de división.
