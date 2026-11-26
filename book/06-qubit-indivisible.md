# 6. El qubit indivisible: interferencia vista desde lo estocástico

> Código: `IndivisibleStochasticMechanics/Examples/Qubit.lean`

Este es el primer resultado "con física" del proyecto: un sistema cuántico concreto cuyo
proceso estocástico **demostramos** que es indivisible.

## El sistema

Dos configuraciones, $\mathcal{C} = \{0, 1\}$, con hamiltoniano $H = \sigma_x$. La
evolución es

$$U(t) = e^{-it\sigma_x} = \cos t\,\mathbb{1} - i\sin t\,\sigma_x = \begin{pmatrix}\cos t & -i\sin t\\ -i\sin t & \cos t\end{pmatrix},$$

y la regla de Born da

$$\Gamma(t) = \begin{pmatrix}\cos^2 t & \sin^2 t\\ \sin^2 t & \cos^2 t\end{pmatrix}.$$

Es la dinámica de las **oscilaciones de Rabi**: el sistema pasa de $0$ a $1$ y vuelve.

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

## Ejercicios

1. (Papel) Mostrá que $t'=\pi/2$ **sí** es un evento de división. Pista: $\Gamma(\pi/2)$
   es una permutación, así que tiene inversa estocástica.
2. (Papel) Mostrá que **ningún** $t' \in (0, \pi/2)$ es un evento de división. Pista:
   escribí $\Gamma(t) = \tfrac12(\mathbb{1} + \lambda(t)\,\sigma_x)$ con $\lambda(t) = \cos 2t$
   y usá el ejercicio 2 del capítulo 4.
3. (Lean) Formalizá los dos ejercicios anteriores. Es una tarea abierta del roadmap.
4. (Para pensar) En $\pi/2$ el sistema "se reinicia". ¿Es una coincidencia que sea
   justo cuando $U(\pi/2)$ es, salvo fases, una permutación?
