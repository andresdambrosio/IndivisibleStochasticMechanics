# 9. La medición y la regla de Born

> Código: `IndivisibleStochasticMechanics/Quantum/Measurement.lean`

## El problema

La regla de Born es el corazón de la mecánica cuántica de libro. Si medimos un
observable con autovectores ortonormales $\{v_a\}$ sobre un estado $\psi$, obtenemos el
resultado $a$ con probabilidad
$$P(a) = |\langle v_a, \psi\rangle|^2 .$$
Pero en la formulación usual esto es un **postulado**, y además invoca una noción
primitiva de "medición" que la teoría nunca define. Ese es el problema de la medición.

En los capítulos anteriores solo obtuvimos probabilidades de **configuraciones**, es
decir, de los observables que son diagonales en la base de configuraciones. ¿Y el resto?
¿Qué pasa si medimos algo cuyos autovectores no son configuraciones, como $\sigma_x$ en un
qubit cuyas configuraciones son los autoestados de $\sigma_z$?

## La respuesta estocástica

El argumento de esta sección es de Barandes ([Barandes, 2023a](https://arxiv.org/abs/2302.10778)). El modelo de medición es el de
von Neumann ([1932, cap. VI](https://doi.org/10.1515/9781400889921)).

En la mecánica estocástica indivisible **solo las configuraciones son físicas**. Una
medición no es una operación especial: es una **interacción física** entre el sistema y un
aparato. El aparato también tiene configuraciones, porque la aguja de un instrumento está
en algún lado. El resultado de la medición *es* la configuración del puntero.

Por lo tanto, la probabilidad de un resultado es la probabilidad de una configuración del
sistema compuesto (sistema + aparato). Esa es una probabilidad de transición ordinaria
del proceso estocástico compuesto. No hace falta ningún postulado nuevo.

Lo que hay que demostrar es que **esas probabilidades coinciden con las de Born**.

## El modelo

- **Sistema:** configuraciones $j \in \mathcal{C}$.
- **Puntero:** una configuración de reposo, *ready*, y una configuración $a$ por cada
  resultado posible. En Lean es `Option n`: `none` es *ready* y `some a` muestra $a$.
- **Observable:** sus autovectores $v_a$ son las columnas de una matriz unitaria $V$.
  Escribimos $P_a = |v_a\rangle\langle v_a|$ para el proyector sobre cada uno.

**Definición (medición ideal de von Neumann).** Es una unitaria $M$ sobre sistema ⊗
puntero que, con el puntero en reposo, actúa así:
$$M\big(|j\rangle \otimes |\text{ready}\rangle\big) = \sum_a P_a|j\rangle \otimes |a\rangle .$$
En palabras: el puntero pasa a mostrar $a$ correlacionado con la componente del sistema
a lo largo de $v_a$.

## La matemática

**Teorema (existencia).** Todo observable, dado por una base ortonormal de autovectores,
tiene una interacción de medición ideal.

*Demostración.* Es el mismo truco del capítulo 8. Los vectores
$c_j = \sum_a P_a|j\rangle\otimes|a\rangle$ son ortonormales:
$$\langle c_j, c_k\rangle = \sum_a \langle j|P_a P_a|k\rangle = \sum_a \langle j|P_a|k\rangle = \langle j|k\rangle = \delta_{jk},$$
porque los $P_a$ son proyectores que suman la identidad. Después se completan a una
unitaria con el lema de `ForMathlib`. $\blacksquare$

**Teorema (regla de Born a partir de configuraciones).** Si el sistema está en el estado
$\psi$ y el puntero en reposo, después de la medición ideal la probabilidad de que el
puntero muestre $a$ es
$$\sum_i \big|\big(M(\psi\otimes|\text{ready}\rangle)\big)_{(i,a)}\big|^2 = |\langle v_a, \psi\rangle|^2 .$$

*Demostración.* La componente $(i, a)$ del estado final es
$(P_a\psi)_i = (v_a)_i\,\langle v_a,\psi\rangle$. Sumando sobre las configuraciones $i$ del
sistema:
$$\sum_i |(v_a)_i|^2\,|\langle v_a,\psi\rangle|^2 = |\langle v_a,\psi\rangle|^2,$$
porque $v_a$ está normalizado. $\blacksquare$

**Corolario (la regla de Born en lenguaje estocástico).** Supongamos que el sistema
empieza en la configuración $j$, evoluciona con $U$ y después se mide. La probabilidad de
que el puntero termine en la configuración $a$ es
$$|\langle v_a|U|j\rangle|^2 .$$
Este número es una **probabilidad de transición del proceso estocástico compuesto**, cuya
evolución es la unitaria $M\,(U\otimes\mathbb{1})$, sumada sobre la configuración final
del sistema.

## Qué ganamos

El argumento es de Barandes, y el modelo de medición, de von Neumann. Lo que aporta este
capítulo es la versión formal, verificada en Lean. Antes, la regla de Born para observables arbitrarios era un postulado. Ahora es un teorema
que dice lo siguiente: **si el aparato es un sistema físico más y los resultados son sus
configuraciones, las probabilidades de los resultados son las de Born**. Solo usamos dos
cosas: la regla para configuraciones, que en esta teoría es la definición de las
probabilidades de transición, y la física de la interacción.

## Lo que todavía falta

Este es el primer paso, no el argumento completo. Está anotado en `TRUSTED.md` y en el
roadmap.

- **Observables degenerados:** acá cada resultado tiene un único autovector. El caso
  general requiere proyectores de rango mayor.
- **Mediciones no ideales y POVM:** aparatos ruidosos o imperfectos.
- **El "colapso":** queremos demostrar que después de la medición hay un **evento de
  división**. El sistema compuesto "se reinicia" y la evolución posterior depende solo
  del resultado registrado. En esta teoría, el colapso no es más que condicionar
  probabilidades ordinarias en un evento de división. Lo demostramos en el
  [capítulo 10](10-collapse-and-decoherence.md).

## En Lean

```lean
def IsIdealMeasurement (V : Matrix n n ℂ) (M : Matrix (n × Option n) (n × Option n) ℂ) :
    Prop :=
  M ∈ unitaryGroup (n × Option n) ℂ ∧
    ∀ i j, M (i, none) (j, none) = 0 ∧ ∀ a, M (i, some a) (j, none) = V i a * star (V j a)
```

La entrada $(i, a), (j, \text{ready})$ es $V_{ia}\overline{V_{ja}} = (P_a)_{ij}$. Las
entradas con el puntero en reposo al final son cero: después de medir, el puntero siempre
muestra algo.

```lean
theorem IsIdealMeasurement.pointer_prob (hV : V ∈ unitaryGroup n ℂ)
    (hM : IsIdealMeasurement V M) (ψ : n → ℂ) (a : n) :
    ∑ i, ‖(M *ᵥ readyState ψ) (i, some a)‖ ^ 2 = ‖(Vᴴ *ᵥ ψ) a‖ ^ 2

theorem IsIdealMeasurement.prob_after_evolution (hV : V ∈ unitaryGroup n ℂ)
    (hM : IsIdealMeasurement V M) (j a : n) :
    ∑ i, ‖(M * (U ⊗ₖ (1 : Matrix (Option n) (Option n) ℂ))) (i, some a) (j, none)‖ ^ 2 =
      ‖(Vᴴ * U) a j‖ ^ 2
```

`(Vᴴ *ᵥ ψ) a` es $\langle v_a, \psi\rangle$, y `U ⊗ₖ 1` es el producto de Kronecker
$U \otimes \mathbb{1}$: el sistema evoluciona y el puntero queda quieto.

## Ejercicios

1. (Papel) Qubit con configuraciones $|0\rangle, |1\rangle$. Medí $\sigma_x$, cuyos
   autovectores son $|\pm\rangle = (|0\rangle \pm |1\rangle)/\sqrt2$, sobre el estado $|0\rangle$.
   Escribí $V$, la columna de $M$ correspondiente a $|0\rangle\otimes|\text{ready}\rangle$, y
   verificá que el puntero muestra cada resultado con probabilidad $1/2$.
2. (Papel) En el ejercicio anterior, ¿qué columnas de $M$ quedan libres? ¿Afectan algún
   resultado físico?
3. (Para pensar) El teorema no usa en ningún lado que $M$ sea unitaria, salvo para que
   exista como evolución física. ¿Por qué importa igual exigirlo?
4. (Lean, abierto) Extendé `IsIdealMeasurement` a observables degenerados.
