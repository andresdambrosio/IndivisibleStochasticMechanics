# 0. Prefacio

## Qué es este libro

Es el cuaderno de bitácora de un proyecto con dos objetivos:

1. Tomar la reformulación de la mecánica cuántica propuesta por **Jacob Barandes**
   (Harvard), en la que los sistemas cuánticos son *procesos estocásticos indivisibles*,
   y **verificar cada uno de sus teoremas con un asistente de demostración**: Lean 4.
2. A partir de ahí, **extenderla** para que cubra todo lo que hace la mecánica cuántica
   de libro de texto, y averiguar si en algún punto dice algo nuevo.

La inspiración viene de lo que está ocurriendo en matemática. Con Lean y su biblioteca
**Mathlib**, miles de personas formalizan matemática de forma colaborativa: cada teorema
lo comprueba una computadora y nadie tiene que "confiar" en una demostración. Queremos
lo mismo para un programa concreto de fundamentos de la física.

## A quién está dirigido

A estudiantes de física o matemática que hayan visto álgebra lineal y un primer curso de
mecánica cuántica. No hace falta saber Lean: el capítulo 2 explica lo necesario y cada
capítulo comenta el código línea por línea.

## Cómo leerlo

Cada capítulo tiene la misma estructura:

- **La idea física**: qué queremos capturar y por qué importa.
- **La matemática**: definiciones y teoremas, con demostraciones en papel.
- **En Lean**: cómo se escribió eso en el repositorio y qué hace cada parte.
- **Ejercicios**: algunos de lápiz y papel y otros de Lean. Varios ejercicios de Lean son
  tareas reales pendientes del proyecto.

## Cómo seguirlo con el código

```bash
git clone https://github.com/andresdambrosio/IndivisibleStochasticMechanics
cd IndivisibleStochasticMechanics
lake exe cache get
lake build
```

Si `lake build` termina sin errores, todas las demostraciones del libro que están
marcadas como verificadas lo están de verdad en tu máquina.

## Sobre el nombre

Barandes habla de *indivisible stochastic processes* y de la *stochastic-quantum
correspondence*. Nosotros llamamos al conjunto **Mecánica Estocástica Indivisible**
(*Indivisible Stochastic Mechanics*, ISM). Ojo: no hay que confundirla con la *mecánica
estocástica* de Edward Nelson (1966), que es una teoría distinta basada en procesos de
difusión markovianos.
