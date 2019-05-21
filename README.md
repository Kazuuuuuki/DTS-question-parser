# DTS-question-parser

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

- 問題のファイル `testset/question01.ccg`  etc.
- 答えのファイル `testset/question01.answer` etc.
- `results/main.html` に結果の一覧が表示される。
- `coqlib.v` にCoqのタクティクスを書く。 `nltac` が実行されるタクティクス名。

## CCG木の書き方

`sentences/example1.ccg` を参考にする。

```
(S (NP John) (S\NP runs))
(S (NP John) (S\NP (<S\NP>/NP likes) (NP Mary)))
(S (<S/<S\NP>> (<S/<S\NP>>/N every) (N boy)) (S\NP sleeps))
(S (<S/<S\NP>> (<S/<S\NP>>/N some) (N boy)) (S\NP sleeps))
(S (S (NP John) (S\NP runs)) (S\S .))
```

### 注意

統語範疇のかっこは `<...>` を使う。例えば、 `(S\NP)/(S\NP)` は
`<S\NP>/<S\NP>` と書く。

## テンプレートの書き方

- テンプレートは、 `semantic_lexicon_for_question.yaml`

- テンプレート・公理では、以下の論理記号を使う。

```
否定            -A
連言            A & B
選言            A | B
条件法          A -> B
Pi型           pi(A, \x.B)
Sigma型        sig(A, \x.B)
Existential型  ex(A, \x.B)
pi_1 u         projT1(u)
pi_2 u         projT2(u)
等号           x = y
ラムダ         \x. A
```

#### カッコについての注意!!

```
exists x. F(x) & G(x) は (exists x. F(x)) & G(x) 
```
と読まれてしまうので
```
exists x. (F(x) & G(x)) 
```
と書かないといけない。

## 中間ファイルとエラーメッセージ

`./parsing.sh sentences/example1.ccg` を実行すると、 `results/`に以下のような順序で中間ファイルが生成される。

```
example1.ccg（インプットのCCGファイル）
↓
example1.xml（example1.ccgをxmlに変換したもの）
↓
example1.sem.xml（example1.xmlから論理式を生成したもの）
example1.sem.err（テンプレートの不備などにより論理式生成に失敗したときにこのファイルにエラーメッセージが出力される。うまく言っていれば空。）
↓
example1.html（CCG木を論理式付きで可視化したもの）
```

例えば、
```
File does not exist: results/example1.sem.xml
...
```
というエラーは、論理式を生成する example1.sem.xml のところで失敗したことを意味していて、テンプレートに何か問題があるという予想が立てられる。
