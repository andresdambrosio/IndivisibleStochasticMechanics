# Mecánica Estocástica Indivisible

### Un curso que construye, paso a paso y con demostraciones verificadas en Lean, la reformulación estocástica de la mecánica cuántica de Jacob Barandes

**Andrés D'Ambrosio**

> *Read this book in English: use the **EN** button at the top right.*

## Autoría y créditos

La mecánica cuántica como procesos estocásticos indivisibles es una propuesta de
**Jacob A. Barandes** ([arXiv:2302.10778](https://arxiv.org/abs/2302.10778),
[arXiv:2309.03085](https://arxiv.org/abs/2309.03085),
[arXiv:2507.21192](https://arxiv.org/abs/2507.21192)). Las ideas centrales de este libro
son suyas, y también de los autores clásicos que citamos en cada capítulo (Born, von
Neumann, Stinespring, Kraus, Zurek y otros).

Este libro y la formalización en Lean son de **Andrés D'Ambrosio** (o sea, yo), escritos con ayuda
intensiva de IA (ver el [prefacio](00-preface.md)). En cada capítulo cito la fuente de
cada resultado, y marco de forma explícita lo que es un aporte propio del proyecto. La
lista completa está en la [bibliografía](99-references.md). Puedo equivocarme, puede fallar. Espero no haber comito algun error y haber dado el crédito justo a quien corresponda. Si ven algo raro, me avisan a andresdambrosio@gmail.com (o me lo dejan en el repo) y procederé a corregir inmediatamente. Errarem humanum est (Errarem IA est?).

Este libro acompaña al repositorio. Cada capítulo explica la física, la matemática y el
código Lean de un tramo del proyecto. El libro crece a medida que avanza el código. Los
capítulos marcados con ✅ corresponden a código ya verificado. Los marcados con 🚧 son
planes.

## Índice

**Parte I: Punto de partida**

0. ✅ [Prefacio: qué es este libro y cómo leerlo](00-preface.md)
1. ✅ [Por qué reformular la mecánica cuántica](01-motivation.md)
2. ✅ [Lean para físicos, en lo mínimo indispensable](02-lean-for-physicists.md)

**Parte II: Los fundamentos estocásticos**

3. ✅ [Probabilidades y matrices estocásticas](03-stochastic-matrices.md)
4. ✅ [Procesos indivisibles y eventos de división](04-indivisible-processes.md)
5. ✅ [La representación de Born y la evolución unitaria](05-born-representation.md)
6. ✅ [El qubit indivisible: interferencia vista desde lo estocástico](06-indivisible-qubit.md)

**Parte III: La correspondencia completa**

7. ✅ [Matrices densidad y canales cuánticos](07-density-matrices-and-channels.md)
8. ✅ [El teorema estocástico-cuántico: de procesos a espacios de Hilbert](08-stochastic-quantum-theorem.md)
9. ✅ [La medición y la regla de Born](09-measurement-and-born-rule.md)
10. ✅ [Colapso y decoherencia como eventos de división](10-collapse-and-decoherence.md)
11. ✅ [Sistemas compuestos y entrelazamiento](11-composite-systems.md)

**Parte IV: Más allá** 🚧

12. 🚧 Espacios de configuraciones continuos
13. 🚧 Hacia la relatividad y los campos
14. 🚧 Problemas abiertos

[Bibliografía](99-references.md)

## Convenciones

- Los nombres de declaraciones Lean aparecen en `monoespaciado`, por ejemplo
  `ISM.Qubit.process_isIndivisible`. Se pueden buscar directamente en el código.
- Matrices estocásticas **por columnas**: $\Gamma_{ij}$ es la probabilidad de terminar en
  $i$ habiendo empezado en $j$.
- Unidades con $\hbar = 1$.
