FCR(Functional Certificate for Rewriting)

* Install
---------
cabal install

* Usage
--------
In the terminal, type: ''fcr'', this will load the fcr environment. 

* Some common commands
------------------------
The fcr environment support the following commands.

1. :l <filename>

e.g. :l examples/inner2.rs
This will check and load a given file(for the format of the file please see the example). 
The checkings in this case are: guardness check, type check and proof check.

The following commands assume a file containing rewrite rules is loaded without errors,
we will use examples/inner2.rs as running example.


2. :env 
This will print out the current environment information

3. :inner <number> (<term>)

e.g. :inner 10 (F (S x) (G (H x Z)))
This will apply the rewrite rules to rewrite the term (F (S x) (G (H x Z))), 
the bound for rewriting is 10 step, and the strategy is leftmost-innermost.

4. :outer <number> (<term>)

e.g. :outer 10 (F (S x) (G (H x Z)))
This will apply the rewrite rules to rewrite the term (F (S x) (G (H x Z))),
the bound for rewriting is 10 step, and the strategy is leftmost-outermost.

5. :full <number> (<term>)

e.g. :full 2 (F (S x) (G (H x Z)))
This will display the tree of rewriting the term (F (S x) (G (H x Z))), 
the depth of the tree is 2.

6. :q

Quit fcr.

* Examples
---------
See directory examples/



