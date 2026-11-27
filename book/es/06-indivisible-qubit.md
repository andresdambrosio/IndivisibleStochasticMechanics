# 6. El qubit indivisible: interferencia vista desde lo estocástico

> Código: `IndivisibleStochasticMechanics/Examples/Qubit.lean`

Este es el primer resultado "con física" del proyecto: un sistema cuántico concreto cuyo
proceso estocástico **demostramos** que es indivisible.

La tesis de que la interferencia y la indivisibilidad son dos caras del mismo fenómeno es
de Barandes ([Barandes, 2023a](https://arxiv.org/abs/2302.10778)). El ejemplo concreto, con este hamiltoniano y estos instantes,
lo armamos para este curso, y la demostración formal en Lean es nuestra.

## El sistema

Dos configuraciones, $\mathcal{C} = \{0, 1\}$, con hamiltoniano $H = \sigma_x$. La
evolución es

$$U(t) = e^{-it\sigma_x} = \cos t\,\mathbb{1} - i\sin t\,\sigma_x = \begin{pmatrix}\cos t & -i\sin t\\ -i\sin t & \cos t\end{pmatrix},$$

y la regla de Born da

$$\Gamma(t) = \begin{pmatrix}\cos^2 t & \sin^2 t\\ \sin^2 t & \cos^2 t\end{pmatrix}.$$

Es la dinámica de las **oscilaciones de Rabi** ([Rabi, 1937](https://doi.org/10.1103/PhysRev.51.652)):
el sistema pasa de $0$ a $1$ y vuelve.

## Tres instantes clave

| $t$ | $\Gamma(t)$ | Interpretación |
|---|---|---|
| $0$ | $\begin{pmatrix}1&0\\0&1\end{pmatrix}$ | no pasó nada |
| $\pi/4$ | $\begin{pmatrix}1/2&1/2\\1/2&1/2\end{pmatrix}$ | mezcla total: la configuración actual no dice nada de la inicial |
| $\pi/2$ | $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ | intercambio determinista: $0 \to 1$ y $1 \to 0$ con certeza |

## El argumento

**Teorema.** $t' = \pi/4$ no es un evento de división. Por tanto, el proceso es indivisible.

*Demostración.* Supongamos que lo fuera. Entonces existiría una matriz $\Delta$ con
$\Gamma(\pi/2) = \Delta\,\Gamma(\pi/4)$. Pero las dos columnas de $\Gamma(\pi/4)$ son
iguales, ambas $(1/2,1/2)^T$. Las columnas de $\Delta\,\Gamma(\pi/4)$ son $\Delta$ aplicada
a las columnas de $\Gamma(\pi/4)$, así que también son iguales entre sí. Y las columnas
de $\Gamma(\pi/2)$ son $(0,1)^T$ y $(1,0)^T$, que son distintas. Contradicción.
$\blacksquare$

Hay un detalle notable: **ni siquiera hace falta que $\Delta$ sea estocástica**. Ninguna
ley lineal puede "des-mezclar" a partir de una distribución que ya olvidó la condición
inicial.

## Qué significa físicamente

En $\pi/4$ el sistema está en $0$ o en $1$ con probabilidad $1/2$, *sea cual sea* la
configuración inicial. Si el proceso fuera markoviano, la configuración en $\pi/4$ sería
todo lo que importa para el futuro, y el sistema habría perdido para siempre la memoria
de dónde empezó. Sin embargo, en $\pi/2$ "recuerda" perfectamente: el resultado depende
con certeza de la configuración inicial.

En lenguaje cuántico, eso es **interferencia**: las amplitudes se recombinan de forma
coherente. En lenguaje estocástico, es **indivisibilidad**: las leyes condicionan respecto
del instante $0$, no respecto del instante $\pi/4$. Son dos descripciones del mismo
fenómeno, y esa es la tesis de Barandes en un caso concreto.

## En Lean

La evolución unitaria:

```lean
noncomputable def U (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.cos t : ℂ), -I * Real.sin t; -I * Real.sin t, Real.cos t]
```

`!![a, b; c, d]` es la notación de Mathlib para matrices escritas explícitamente.
Probamos que es unitaria (`U_mem_unitaryGroup`) y que `U 0 = 1` (`U_zero`). Con eso,
el capítulo anterior nos da el proceso gratis:

```lean
noncomputable def process : GenStochasticProcess (Fin 2) :=
  GenStochasticProcess.ofUnitary U U_mem_unitaryGroup U_zero
```

Calculamos $\Gamma(t)$ explícitamente (`process_Γ`) y después viene el teorema central:

```lean
theorem not_isDivisionEvent_pi_div_four : ¬ process.IsDivisionEvent (Real.pi / 4) := by
  rintro ⟨-, Δ, hΔ⟩
  have h := (hΔ (Real.pi / 2) (by linarith [Real.pi_pos])).2
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  simp [process_Γ, Matrix.mul_apply, Fin.sum_univ_two] at h00 h01
  linarith
```

Línea por línea:
1. `rintro ⟨-, Δ, hΔ⟩`: "supongamos que es un evento de división, con testigo $\Delta$".
2. `have h := ...`: aplicamos la hipótesis en $t = \pi/2$, después de comprobar que
   $\pi/2 \geq \pi/4$.
3. `h00`, `h01`: miramos las entradas $(0,0)$ y $(0,1)$ de la igualdad matricial.
4. `simp`: sustituye los valores concretos. Las entradas quedan
   - $(0,0)$: $0 = \tfrac12\Delta_{00} + \tfrac12\Delta_{01}$
   - $(0,1)$: $1 = \tfrac12\Delta_{00} + \tfrac12\Delta_{01}$
5. `linarith`: de ahí sale $0 = 1$, absurdo.

Es exactamente el argumento de "columnas iguales" en papel, restringido a la primera
fila. Finalmente:

```lean
theorem process_isIndivisible : process.IsIndivisible := fun h =>
  not_isDivisionEvent_pi_div_four (h _ (by positivity))
```

"Si fuera divisible, $\pi/4$ sería un evento de división, y acabamos de ver que no lo es."

## Todos los eventos de división

El argumento para $\pi/4$ usó que las columnas de $\Gamma(\pi/4)$ son iguales. Los otros
instantes necesitan otro argumento, y ese argumento da la respuesta completa.

**Teorema.** $t' \geq 0$ es un evento de división del qubit si y solo si $t'$ es un
múltiplo de $\pi/2$: $t' \in \{0, \pi/2, \pi, 3\pi/2, \dots\}$.

*Demostración.* Si $t' = k\pi/2$, entonces $\Gamma(t')$ es la identidad ($k$ par) o el
intercambio ($k$ impar). En los dos casos $\Gamma(t')^2 = \mathbb{1}$, así que
$\Delta(t \leftarrow t') = \Gamma(t)\,\Gamma(t')$ sirve: es un producto de matrices
estocásticas, por lo tanto estocástica, y $\Delta\,\Gamma(t') = \Gamma(t)\,\Gamma(t')^2 = \Gamma(t)$.

Si $t'$ no es múltiplo de $\pi/2$, entonces $c = \cos^2 t'$ y $s = \sin^2 t'$ son los dos
estrictamente positivos. Tomemos un instante posterior $t \geq t'$ en el que el sistema
se intercambió, $\Gamma(t) = \begin{pmatrix}0&1\\1&0\end{pmatrix}$ (cualquier
$t = m\pi + \pi/2$ con $m$ suficientemente grande). La primera fila de
$\Gamma(t) = \Delta\,\Gamma(t')$ dice

$$0 = \Delta_{00}\,c + \Delta_{01}\,s, \qquad 1 = \Delta_{00}\,s + \Delta_{01}\,c.$$

$\Delta$ es estocástica, así que sus entradas son no negativas. En la primera ecuación,
una suma de términos no negativos da $0$, y $c, s > 0$, así que $\Delta_{00} = \Delta_{01} = 0$.
Entonces la segunda ecuación dice $1 = 0$. $\blacksquare$

Acá, a diferencia de $\pi/4$, que $\Delta$ sea estocástica es esencial. Siempre que
$\cos 2t' \neq 0$, que es el determinante de $\Gamma(t')$, la inversa existe y
$\Delta = \Gamma(t)\,\Gamma(t')^{-1}$ resuelve la ecuación. Solo que tiene entradas negativas:
es una ley *lineal* válida, pero no *estocástica*.

El panorama es claro. El proceso "se reinicia" justo en los instantes en que $\Gamma$ es
una permutación, es decir, cuando la configuración en $t'$ determina la inicial. Entre
esos instantes es indivisible. La caracterización es un cálculo directo hecho para este
curso; la idea general de que los eventos de división son los instantes en que el proceso
se puede reiniciar es de Barandes ([Barandes, 2023a](https://arxiv.org/abs/2302.10778)).

En Lean:

```lean
theorem isDivisionEvent_iff_exists_nat (t' : ℝ) :
    process.IsDivisionEvent t' ↔ ∃ k : ℕ, t' = k * (Real.pi / 2)

theorem isDivisionEvent_pi_div_two : process.IsDivisionEvent (Real.pi / 2)

theorem not_isDivisionEvent_of_mem_Ioo {t' : ℝ} (ht : t' ∈ Set.Ioo 0 (Real.pi / 2)) :
    ¬ process.IsDivisionEvent t'
```

El núcleo es `isDivisionEvent_iff`, que enuncia la condición como $\sin 2t' = 0$
(recordá que $\sin 2t' = 2 \sin t' \cos t'$). La prueba sigue el argumento en papel: el
instante posterior es `m * π + π / 2` con `m = ⌈t' / π⌉₊` (el techo, un número natural), y
`nonneg_of_mem_colStochastic` da las entradas no negativas de $\Delta$.

## Ejercicios

1. (Papel) Da una segunda prueba de que ningún $t' \in (0, \pi/2)$ distinto de $\pi/4$ es
   un evento de división. Escribí
   $\Gamma(t) = \tfrac12\begin{pmatrix}1+\lambda & 1-\lambda\\ 1-\lambda & 1+\lambda\end{pmatrix}$
   con $\lambda = \cos 2t$, calculá $\Gamma(t)\,\Gamma(t')^{-1}$ y usá el ejercicio 2 del
   capítulo 4.
2. (Papel) Calculá explícitamente $\Delta = \Gamma(\pi/2)\,\Gamma(\pi/6)^{-1}$ y encontrá sus
   entradas negativas.
3. (Lean) Probá que $\Gamma$ tiene período $\pi$: `process.Γ (t + Real.pi) = process.Γ t`.
   Pista: `process_Γ`, `Real.cos_add_pi`, `Real.sin_add_pi`.
4. (Para pensar) En $\pi/2$ el sistema "se reinicia". ¿Es una coincidencia que sea
   justo cuando $U(\pi/2)$ es, salvo fases, una permutación?
