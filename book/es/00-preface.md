# 0. Prefacio

## Qué es este libro

Es el cuaderno de bitácora de un proyecto con dos objetivos:

1. Tomar la reformulación de la mecánica cuántica propuesta por **Jacob A. Barandes**
   (Harvard) en [Barandes, 2023a](https://arxiv.org/abs/2302.10778),
   [Barandes, 2023b](https://arxiv.org/abs/2309.03085) y
   [Barandes, 2025](https://arxiv.org/abs/2507.21192), en la que los sistemas cuánticos son
   *procesos estocásticos indivisibles*, y **verificar cada uno de sus teoremas con un asistente de demostración**: Lean 4.
2. A partir de ahí, **extenderla** para que cubra todo lo que hace la mecánica cuántica
   de libro de texto, y averiguar si en algún punto dice algo nuevo.

La inspiración viene de lo que está ocurriendo en matemática. Con
[Lean 4](https://lean-lang.org/) ([de Moura y Ullrich, 2021](https://doi.org/10.1007/978-3-030-79876-5_37))
y su biblioteca **Mathlib** ([The mathlib Community, 2020](https://arxiv.org/abs/1910.09336)), miles de personas
formalizan matemática de forma colaborativa: cada teorema lo comprueba una computadora y nadie tiene que "confiar" en una demostración. Queremos
lo mismo para un programa concreto de fundamentos de la física.

## Autoría

El libro y la formalización son de **Andrés D'Ambrosio**. La teoría que se formaliza es de
Jacob Barandes, y los resultados clásicos que usamos son de sus respectivos autores. En
cada capítulo decimos de quién es cada idea, con la cita y el link. Cuando algo es un
aporte propio del proyecto (una demostración formal, una construcción o un ejemplo nuevo)
lo decimos explícitamente. La lista completa de fuentes está en la
[bibliografía](99-references.md).

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

## Cómo trabajamos: IA y la capa de confianza

Este proyecto se hace con ayuda intensiva de inteligencia artificial, y no lo
escondemos: es parte del experimento. La pregunta obvia es por qué deberías confiar en
algo escrito en buena parte por una IA. La respuesta tiene dos partes.

**Las demostraciones no necesitan confianza.** Lean comprueba cada paso. Si el archivo
compila, la demostración es correcta, sin importar quién o qué la escribió. Por eso la IA
puede escribir demostraciones sin límite.

**Las definiciones sí necesitan confianza.** Lean comprueba que demostramos *lo que
escribimos*, pero no que lo escrito sea *lo que la física quiere decir*. Si definimos mal
"evento de división", todos los teoremas sobre eventos de división quedan perfectamente
verificados y son perfectamente irrelevantes. Ninguna computadora puede detectar ese
error, porque es un error de *significado*.

Por eso el proyecto tiene una **capa de confianza**: el archivo `TRUSTED.md` lista cada
definición y cada enunciado principal, qué pretende capturar, de qué paper sale y si ya
lo revisó una persona (✅) o todavía no (⏳). La CI impide agregar una definición nueva
sin registrarla ahí. Toda la confianza humana se concentra en esa capa, que es pequeña,
y el resto puede crecer tanto como haga falta.

A lo largo del libro, cuando presentemos una definición, discutiremos las **decisiones de
interpretación** que tomamos al formalizarla. Esas discusiones son física, no
programación, y son la parte más importante del curso.

## Sobre el nombre

Barandes habla de *indivisible stochastic processes* y de la *stochastic-quantum
correspondence*. En este curso usamos **Mecánica Estocástica Indivisible**
(*Indivisible Stochastic Mechanics*, ISM) como nombre corto para el conjunto. Es una
etiqueta nuestra, no una teoría distinta de la de Barandes. Ojo: no hay que confundirla
con la *mecánica estocástica* de Edward Nelson
([Nelson, 1966](https://doi.org/10.1103/PhysRev.150.1079)), que es una teoría distinta
basada en procesos de difusión markovianos.
