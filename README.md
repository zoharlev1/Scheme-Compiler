# Scheme Compiler
ID: 314975418 - Zohar Levi
ID: 315256362 - Mahmoud Mahajna
## Git


### Vagrant

This repository contains a Vagrant setup file called `Vagrantfile` (paraphrasing on `makefile`). Vagrant is a tool for 
sharing VMs. It includes the VM image, setup, configuration, network connections and just about anything you'd want to 
configure before you start working. The vagrantfile contains all the commands required to setup your VM.


Description:

For the first assignment we implemented an Extended reader for Scheme. Our reader supports almost all of the Scheme S-expressions, it's case insensitivity excluding 
chars and strings, supports different type of comments and whitespaces. 
[hw1 (4).pdf](https://github.com/zoharlev1/Scheme-Compiler/files/9338358/hw1.4.pdf)

For the second assignment, we implemented a tag-parser in Scheme. You shall implement the
procedure tag_parse_expression that takes an sexpr as an argument, and returns a tag-parsed
sexpr of type expr. Parsing in this sense means annotating the sexpr with tags, so that the type
of expression can be known easily and the various sub-expressions can be accessed with confidence and, parsing the sub-expressions as well.
[hw2.pdf](https://github.com/zoharlev1/Scheme-Compiler/files/9338404/hw2.pdf)

The purpose of the third assignment is to add the semantic analysis component to the pipeline of
your compiler. This component shall compute and annotate the lexical addresses of all variables,
annotate applications in tail-position, and box variables that are copied from the stack to the heap,
and that changes to which may be visible elsewhere in the code.
[hw3.pdf](https://github.com/zoharlev1/Scheme-Compiler/files/9338412/hw3.pdf)

The last project, was built ontop of all the previous parts- Reader, Tag Parser and Semantic Analyzer. 
[proj.pdf](https://github.com/zoharlev1/Scheme-Compiler/files/9338419/proj.pdf)


