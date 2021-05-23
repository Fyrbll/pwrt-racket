# Racket Code for Programming with Refinement Types

I have tried my best to translate the Liquid Haskell code for chapters 2, 3 and
4 of [Programming with Refinement
Types](http://ucsd-progsys.github.io/lh-workshop/01-index.html) into Typed
Racket.

If you just want the code with some observations you can read either **pwrt.md**
or **pwrt.pdf** and ignore all the other files. It's meant to be a companion to
the first few chapters of Programming with Refinement Types, rather than a
replacement.

The files in this repository, other than **README.md**, are:

- **pwrt.md**, the markdown text of my translation containing the code
interspersed with comments.
- **pwrt.rkt**, just the code so that you can play around with it and ensure
that it compiles.
- **makefile**, so that when you run `make` (assuming you have the `pandoc` and
`pdflatex` binaries), you get a PDF version of **pwrt.md** with Racket syntax
highlighting. 
- **pwrt.pdf**, generated from **pwrt.md** by running `make` on my computer so
that you don't have to.
- **racket.xml**, a Pandoc-compatible syntax definition file for that lets
it highlight Racket code.

I'd love to hear your comments, suggestions for improvement and alternate
approaches to problems. You can post them in the Issues tab. Thank you!
