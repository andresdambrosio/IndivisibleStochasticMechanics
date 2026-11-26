# Mecánica Estocástica Indivisible

### Un curso que construye, paso a paso y con demostraciones verificadas en Lean, la reformulación estocástica de la mecánica cuántica de Jacob Barandes

Este libro acompaña al repositorio. Cada capítulo explica la física, la matemática y el
código Lean de un tramo del proyecto. El libro crece a medida que avanza el código. Los
capítulos marcados con ✅ corresponden a código ya verificado. Los marcados con 🚧 son
planes.

## Índice

**Parte I: Punto de partida**

0. ✅ [Prefacio: qué es este libro y cómo leerlo](00-prefacio.md)
1. ✅ [Por qué reformular la mecánica cuántica](01-motivacion.md)
2. ✅ [Lean para físicos, en lo mínimo indispensable](02-lean-para-fisicos.md)

**Parte II: Los fundamentos estocásticos**

3. ✅ [Probabilidades y matrices estocásticas](03-matrices-estocasticas.md)
4. ✅ [Procesos indivisibles y eventos de división](04-procesos-indivisibles.md)
5. ✅ [La representación de Born y la evolución unitaria](05-representacion-de-born.md)
6. ✅ [El qubit indivisible: interferencia vista desde lo estocástico](06-qubit-indivisible.md)

**Parte III: La correspondencia completa** 🚧

7. ✅ [Matrices densidad y canales cuánticos](07-matriz-densidad-y-canales.md)
8. ✅ [El teorema estocástico-cuántico: de procesos a espacios de Hilbert](08-teorema-estocastico-cuantico.md)
9. ✅ [La medición y la regla de Born](09-medicion-y-regla-de-born.md)
10. 🚧 Decoherencia y colapso como eventos de división
11. 🚧 Sistemas compuestos y entrelazamiento

**Parte IV: Más allá** 🚧

12. 🚧 Espacios de configuraciones continuos
13. 🚧 Hacia la relatividad y los campos
14. 🚧 Problemas abiertos

## Convenciones

- Los nombres de declaraciones Lean aparecen en `monoespaciado`, por ejemplo
  `ISM.Qubit.process_isIndivisible`. Se pueden buscar directamente en el código.
- Matrices estocásticas **por columnas**: $\Gamma_{ij}$ es la probabilidad de terminar en
  $i$ habiendo empezado en $j$.
- Unidades con $\hbar = 1$.
