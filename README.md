# DTS-question-parser
Codebase for 
### Requirement

- python >= 3.6.5
- [ccg2lambda](https://github.com/mynlp/ccg2lambda)
- coq = coq8.5pl3
   

### Installation
You need to install and set up [ccg2lambda](https://github.com/mynlp/ccg2lambda) in your home directory.
Please check coq's version in your environment. We test our code in Coq8.5pl3. 

### Setting
The testset is in ([testset](https://github.com/Kazuuuuuki/DTS-question-parser/tree/master/testset)).  
The result of parsing and inferencing the testset with Coq is in ([result](https://github.com/Kazuuuuuki/DTS-question-parser/tree/master/results)).  
The semantic template and coqfile which we used in our parser are ([semantic_template](https://github.com/Kazuuuuuki/DTS-question-parser/blob/master/semantic_lexicon_for_question.yaml)) and ([coq_file](https://github.com/Kazuuuuuki/DTS-question-parser/blob/master/coqlib.v)) respectively.


### Usage
You can parse your input data: 

```
./parsing.sh testset/question01.ccg
```

You can see the result of parsing in `results/question01.html`.

### Evaluation
You can parse all inputs in `testset`:

```
./run_test.sh
```
## Input
- testcase `testset/question01.ccg`  etc.
- it's answer `testset/question01.answer` etc.

You can see the all results in `results/main.html`.

The code of proof automation is in `coqlib.v`.


## Notation of CCG Tree

Please consider `sentences/example1.ccg` as example.

```
(S (NP John) (S\NP runs))
(S (NP John) (S\NP (<S\NP>/NP likes) (NP Mary)))
(S (<S/<S\NP>> (<S/<S\NP>>/N every) (N boy)) (S\NP sleeps))
(S (<S/<S\NP>> (<S/<S\NP>>/N some) (N boy)) (S\NP sleeps))
(S (S (NP John) (S\NP runs)) (S\S .))
```

## Remark for input.

`<...>` serves as ().

For example, `<S\NP>/<S\NP>` means `(S\NP)/(S\NP)`.

## Rules of semantic template

- The template we use is `semantic_lexicon_for_question.yaml`

- Notation

```
negation               -A
conjunction          A & B
disjunction          A | B
implication          A -> B
Pi-type           pi(A, \x.B)
Sigma-type        sig(A, \x.B)
Existential-type  ex(A, \x.B)
pi_1 u            projT1(u)
pi_2 u            projT2(u)
equal                x = y
lambda               \x. A
```

### Remarks
```
exists x. F(x) & G(x) is read as (exists x. F(x)) & G(x) 
```
So, you have to write:
```
exists x. (F(x) & G(x)) 
```

### Citation

