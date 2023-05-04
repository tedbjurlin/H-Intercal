# H-Intercal

### Project Concept

This Intercal-72 compiler is my final project submission for the 2023 CSCI-360 Programming Languages class at Hendrix College.

The intent of this project is to build a functioning Intercal-72 compiler in Haskell. Intercal-72 is the first well-known esolang, and was designed with one core philosophy in mind: To be as different from every other currently existing programming language as possible. As such, the only language feature that it shares with its contemporaries is variable assignment. To find out more about Intercal-72 see the [Reference Manual](https://3e8.org/pub/intercal.pdf).

This compiler is intended implement Intercal-72 as accurately as possible, although some differences are unavoidable due to the ambiguous nature of the Reference Manual and the limitations of Haskell as a language.

Example programs can be found in the [examples](examples/) directory. See [INSTALLING](INSTALLING.md) for more information on how to install H-Intercal and run the sample programs.

### Interesting Features

Intercal-72 has a variety of interesting feature (a byproduct of the fact that nearly every feature is unique), but an unexpectedly complex one is the existance of unary boolean operators.

A unary boolean operator takes a single operand, and applies the boolean operation to every adjacent pair of bits, including the first and last. In practice, we can simply apply the operation as a bitwise operation to the operand and itself, bitshifted to the right by one.

Problematically, this requires a method to apply a right shift to an integer where the bits wrap. Haskell does not provide this ability, so I had to come up with my own mathematical approach. This can be seen in the shiftR function in [HIntercal.hs](HIntercal.hs).

Intercal-72 also has a number of unique language features that affect the rest of the program, including the ability to set the mutability of variables, turn on and off language features and specific lines, and stash the values of variables to be retrieved later.

### Project File Structure

The code for this project is split between four different files:

[**HIntercalTypes.hs**](HIntercalTypes.hs): This file contains all of the custom algebraic data types defined for the project. This includes the abstract syntax tree the that the intercal program is parsed into and the error types.

[**HIntercalParser.hs**](HIntercalParser.hs): This file contains the Intercal parser. It parses Intercal file (*.i* file extension) into an abstract syntax tree.

[**HIntercalCheck.hs**](HIntercalCheck.hs): This file contains the funtions to check the abstract syntax tree. These functions check variable names, label names and references, and everything else that can be checked before runtime.

[**Hintercal.hs**](HIntercal.hs): This file contains the main module of the program and the interpreter.

### Challenges

This project took me more than a month to fully implement and fully half of that time was spent doing bugfixes. The design of Intercal-72 is intended to be complex and difficult to understand, and it certainly has stood up to that standard.

The Next, Resume, and Forget operations proved to be especially problematic. As they, put together, effectively serve the function of a Goto, As such, they presented many bugs related to flow control. The Next operation routinely placed control either before or after the intended line, or failed to add the line to the stack and forget and resume regularly returned the wrong item from the nexting stack. Much of my time was spent writing Intercal-72 programs (a challenge in and of itself) that could be used to test certain language features, then trying to identify what bugs had arisen using Intercal-72's intentionally useless error messages.

Input and output are formatted in obnoxious froms: input is taken as a series of space-seperated numbers, written out in english (FOUR THREE OH = 430) and output is given in extended roman numerals. Trying to properly parse and print IO proved frustrating.

The scope of this project just ended up being much larger than I had planned. I did not expect to be working up to the wire, given that I started a week before the project was assigned.