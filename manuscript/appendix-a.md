# Прилог А: Програмирање во Lisp

Во овој дел ќе бидат покажани неколку примери на имплементации на техники што се користат во Z3. Поконкретно, имплементацијата од А.2 соодветствува на клучниот збор `calc`, a имплементацијата од А.3 и А.4 на автоматско докажување на теореми.

Lisp е програмски јазик имплементиран во 1958, година од информатичарот Џон Меккарти (1927 ‒ 2011) [13]. Синтаксите се тие што го прават Lisp таканаречен _симболичен_ јазик ‒ можноста за конструкција и манипулација со симболи. Поради таа намена, тој ќе биде искористен за пример-имплементација на системи за математички докази.

> _Дефиниција А.1_: **Апстрактно синтаксичко дрво** е дрво во коешто се претставуваат команди од изворен код напишан во програмски јазик.

Кога се пишуваат програми во програмски јазик, постои среден чекор што го анализира нивниот изворен код и произведува апстрактно синтаксичко дрво. Потоа, ова дрво се евалуира/пресметува.

![Апстрактно синтаксичко дрво\label{ast}](images/ast.png)

На пример, слика \ref{ast} претставува апстрактно синтаксичко дрво за следниот код:

```
while (a > b) {
    x = x - 1;
    y = y * 2;
}
```

Во Lisp нема ограничување на посебна синтакса како што имаат други програмски јазици. Всушност, пишаниот код ќе биде апстрактното синтаксичко дрво. Оттука, Lisp се залага на минималистички дизајн, со тоа што не постои overhead од дополнителни специјални синтакси.

Во дефиниција 5.1 беа дефинирани формални системи и формален јазик, каде што синтаксата има посебно значење во Lisp. S-expressions ја формираат синтаксата на Lisp.

> _Дефиниција А.2_: Синтаксичките елементи во Lisp се симболични изрази или **S-expressions** [13]. Тие имаат вредност што е листа или симбол.

Со macros како дел од основниот јазик, Lisp-овите имаат можност да ја прошират сопствената синтакса. Macros се всушност многу налик функции, со тоа што се евалуираат на различно ниво.

На пример, со `(list 1 2 3)` се произведува низата $(1, 2, 3)$ и се добива `'(1 2 3)` како резултат. Во овој случај, се искористи `list`, што е вградена функција која прифаќа кој било број на параметри и како резултат, враќа листа генерирана од нив.

Во Lisp се користат загради за означување повик за функција (евалуација). Во принцип, кодот `(f a_1 a_2 ... a_n)` прави евалуација на `f` со `n` параметри. На пример, за функцијата $f(x) = x + 1$, една евалуација е $f(1)$, каде што како повратна вредност се добива 2, а се пишува `(f 2)`. Сепак, како резултат се добива `'(1 2 3)`. Во спротивно, ако се вратеше `(1 2 3)`, тогаш тоа немаше да има смисла, бидејќи, како што беше дискутирано, оваа нотација ќе се обиде да направи повик на функцијата `1` со аргументи `2` и `3`. Наместо тоа, се добива `'(1 2 3)` односно quoted листа ‒ листа во "наводници". Ова е налик на дијагонализацијата во дефиниција 5.29.

Покрај `list`, постојат и други битни вградени функции [21]:

- `cons` ‒ креира пар од две вредности. На пример, `(cons 1 2)` е пар каде што првата вредност е 1, а втората 2
- `car` ‒ ја враќа првата вредност од даден пар. На пример, `(car (cons 1 2))` ќе врати 1
- `cdr` ‒ ја враќа втората вредност од даден пар. На пример, `(cdr (cons 1 2))` ќе врати 2
- `map` ‒ применува функција врз секој елемент од листата. На пример, `(map f '(1 2 3))` ќе врати `(list (f 1) (f 2) (f 3))`

На сличен начин се прави повик кон синтакса (macros). На пример, постои вградена синтакса `quote`. Изразот `'(1 2 3)` е нотација на изразот `(quote (1 2 3))`. Исто така, постои посебна листа наречена празна листа: `(list)` или `(quote ())` или едноставно `'()`. `quote` овозможува создавање на нови симболи и е од особена важност за создавање macros. На пример, `(quote zdravosvet)` го враќа симболот `'zdravosvet`.

Други битни вградени синтакси се:

- `define` ‒ назначува вредност на одредена променлива. На пример, `(define a 1)` го дефинира `a` да биде 1, а секаде каде што се појавува `a` ќе се замени со 1
- `lambda` ‒ креира функција. На пример, `((lambda (x) (+ x 1)) 1)` враќа 2. Друг пример е `(map (lambda (x) (+ x 1)) '(1 2 3))` кој ќе врати `'(2 3 4)`
- `struct` ‒ креира структура, комплексен податок содржан од други комплексни/примитивни податоци. На пример, `(struct kniga (ime avtor))` ќе креира неколку функции:
  ‒ `kniga x y` ‒ за создавање нова книга со име `x` и автор `y`
  ‒ `kniga-ime k` ‒ за преземање име од дадена книга
  ‒ `kniga-avtor k` ‒ за преземање автор од дадена книга
- `cond` ‒ служи за совпаѓање на шеми, слично како во Dafny

Со комбинација на `define` и `lambda`, може да се креираат функции:

```{language=racket}
(define dodadi-1 (lambda (x) (+ x 1)))
```

Во овој случај, `dodadi-1` е функција што додава 1 на некој број. На пример, `(dodadi-1 1)` ќе врати 2. Оваа функција може да се дефинира на поелегантен начин, каде што двете дефиниции се еквивалентни:

```{language=racket}
(define (dodadi-1 x) (+ x 1))
```

На овој начин се врши евалуација, а исто така може да се конструираат овие S-expressions ‒ листи или симболи. Ова е сосема доволно за да може да се програмира во овие системи; оттука минималистичкиот дизајн.

## А.1. Пример: Саморепродуцирачки програми

Со самата моќ што ја има Lisp за обработка на симболи, може на едноставен начин да се напише програма што како резултат ќе го врати кодот на самата програма[^apa1] [1]. Тоа се постигнува со користење на дијагонализација, односно `quote` [8]. Следниот код се надоврзува на примерите од дефиниција 5.29:

```{language=racket}
> (define p (lambda (x) (list 'Boro 'cita x)))
> (p 'kniga)
'(Boro cita kniga)
> (define d (lambda (p x) (p (list 'quote (p x)))))
> (d p 'kniga)
'(Boro cita '(Boro cita kniga))
```

Во другиот пример се користеше дијагонализација во самата дефиниција на `p`, односно важи дека $Q(x) = D(P(x))$:

```{language=racket}
> (define q (lambda (x) (list 'Boro 'cita (d identity x))))
> (define r (lambda (x) (d q x)))
> (equal? (d q 'test) (r 'test))
#t
```

Во дефиницијата на `q` се искористи `(d identity x)`, односно дијагонализација на `x`. Со замена може да се види дека ова е едноставно `(list 'quote x)`. Следно, ќе биде покажан изразот `(list x (list 'quote x))` кој враќа листа што содржи два елемента: `x` и неговата дијагонализација.

```{language=racket}
> (define quine-1 (lambda (x) (list x (list 'quote x))))
```

Доколку се примени `quine-1` и `'quine-1` врз таа функција, се добива следниот резултат:

```{language=racket}
> (quine-1 quine-1)
'(#<procedure:quine-1> '#<procedure:quine-1>)
> (quine-1 'quine-1)
'(quine-1 'quine-1)
```

Во второто извршување се врати истиот код што се искористи, односно самата програма. Ова е причината зошто беше одбран изразот `(list x (list 'quote x))` ‒ неговата евалуација треба да го врати целиот израз.

Конечниот код ќе биде примена на `quote`-ирана верзија од `lambda`-та врз неа:

```{language=racket}
> ((lambda (x) (list x (list 'quote x)))
  '(lambda (x) (list x (list 'quote x))))
'((lambda (x) (list x (list 'quote x)))
  '(lambda (x) (list x (list 'quote x))))
```

Односно извршувањето на програмата ја дава самата дефиниција како резултат.

## А.2. Пример: Резонирање на равенства

Во овој дел ќе бидат дефинирани неколку аксиоми на Пеано, како и функција за замена на равенства за да може да се докажуваат теореми во рамките на овој систем.

Со следниот код се дефинираат неколку од аксиомите на Пеано:

```{language=racket}
(define zero 'z)
(define (succ x) (list 's x))
(define (add-1 a) (list '= (list '+ a zero) a))
(define (add-2 a b) (list '= (list '+ a (succ b)) (succ (list '+ a b))))
```

Во овој случај се искористи `define` за да се дефинираат константи и функции[^apa2]. Имено:

1. `zero` е дефинирано како константа која е всушност симболот `z`
1. `succ` се дефинира како функција што прима еден параметар `x`, а враќа листа што пред `x` се наоѓа симболот `s`. На пример, `(succ zero)` ќе се евалуира во `'(s z)`
1. `add-1` е функција што прима еден параметар `a` а враќа равенство `'(= (+ a zero) a` односно $a + 0 = a$
1. `add-2` е функција што прима два параметри `a` и `b` а враќа равенство `'(= (+ a (succ b)) (succ (+ a b)))` односно $a + S(b) = S(a + b)$

Со следниот код се дефинираат функции за работа со равенства:

```{language=racket}
(define (eq-refl a) (list '= a a))
(define (eq-left a) (cadr a))
(define (eq-right a) (caddr a))
```

`cadr` и `caddr` се вградени функции што го враќаат вториот и третиот елемент од дадена листа, соодветно. Во овој случај се дефинираа три функции: една за конструкција на равенство $a = a$ односно `eq-refl`, друга за извлекување на левата страна на равенството `eq-left` и трета за десната страна на равенството `eq-right`.

Следно, се дефинира алгоритамот за замена во равенство. Дефиницијата е од слична природа со онаа од дефиниција 5.16, но е поедноставена во тоа што не разликува врзани и слободни променливи.

```{language=racket}
(define (subst x y expr)
  (cond ((null? expr) '())
        ((equal? x expr) y)
        ((not (pair? expr)) expr)
        (else (cons (subst x y (car expr))
                    (subst x y (cdr expr))))))
```

Следните две дефиниции ќе служат како помошни функции за презапишување во равенство:

```{language=racket}
(define (rewrite-left eq1 eq2)
  (subst (eq-left eq1) (eq-right eq1) eq2))

(define (rewrite-right eq1 eq2)
  (subst (eq-right eq1) (eq-left eq1) eq2))
```

На крајот, дадена теорема е валидна ако двете страни од равенството се валидни.

```{language=racket}
(define (valid-theorem? theorem)
  (and (equal? theorem (eq-refl (eq-left theorem)))
       (equal? theorem (eq-refl (eq-right theorem)))))
```

Еден пример-доказ се поставува на следниот начин:

```{language=racket}
(define (prove-theorem)
  (define theorem '(= (+ a (s z)) (s a)))               ; a + S(0) = S(a)
  (define step1 (rewrite-left (add-2 'a zero) theorem)) ; S(a + 0) = S(a)
  (define step2 (rewrite-left (add-1 'a) step1))        ; S(a) = S(a)
  step2)
```

Функцијата `prove-theorem` дефинира чекори каде што во секој чекор се трансформира зададената теорема (онаа што треба да се докаже), со тоа што се користи правило на заклучување. На крајот, се враќа последната трансформација `step2`. Во овој случај, `(valid-theorem? (prove-theorem))` ќе врати вистина.

На овој начин се покажа минимален систем за конструирање докази, во кој може да се конструираат равенки и да се прават замени во нив, сличен на командата `calc` во Dafny [4].

## А.3. Пример: Автоматски докажувач на теореми

Во 5.1 беа разгледани формалните системи. Во овој пример, ќе биде имплементиран автоматски докажувач на теореми за даден формален систем [6]. Треба да се специфицира кои се аксиомите и правилата на заклучување, а потоа програмата ќе ги проба сите можни комбинации и ќе врати дали се постигнува конечниот (бараниот) резултат.

На следниот начин се дефинираат податочните структури:

```{language=racket}
; Pravilo e nacin da se smeni teorema
(struct rule (name function) #:transparent)

; Teorema se sodrzi od pocetna aksioma i pravila
(struct theorem (axiom rules result) #:transparent)

; Sistemot za dokazuvac sodrzi lista na aksiomi i inferencijalni pravila
(struct theorem-prover (axioms rules) #:transparent)

; Aksioma e teorema sto e vekje dokazana
(define (axiom a) (theorem (list a) '() a))
```

За да се примени правило врз теорема, се креира нова теорема која е слична на оригиналната, со тоа што правилото е додадено во листата на правила:

```{language=racket}
(define (theorem-apply-rule p t r)
  (theorem (theorem-axiom t)
           (append (theorem-rules t) (list r))
           ((rule-function r) (theorem-result t) p)))
```

Следната функција ќе ги примени сите правила врз сите теореми содржани во дадениот објект `theorem-prover`:

```{language=racket}
(define (theorems-apply-rules-iter prover theorems result)
  (cond
    ((eq? theorems '()) result)
    (else
     (theorems-apply-rules-iter
      prover
      (cdr theorems)
      (append (map (lambda (r) (theorem-apply-rule prover (car theorems) r)) (theorem-prover-rules prover))
              result)))))

; Pomosna funkcija
(define (theorems-apply-rules prover theorems) (theorems-apply-rules-iter prover theorems '()))
```

За да се најде доказ за даден `theorem-prover`, се пребарува низ сите можни резултати и се проверува дали заклучокот се содржи. Ако се содржи, само се враќа. Во спротивно, рекурзивно се градат нови теореми на начин каде што сите правила се применуваат едно по друго.

На пример, за правилата 1, 2 и 3, бесконечното дрво во кое ќе се пребарува со почетна аксиома `o` е:

```
      o________________
     /       \         \
    1____     2         3
   / \   \   / \       / \
  1   2   3 ... ... ...  ...
 / \   \
... ... ...
```

Функцијата за наоѓање докази во вакви бесконечни дрва е:

```{language=racket}
(define (find-proof-iter prover target max-depth found-proofs depth)
  (cond
    ; Slucaj kade dokazot e najden
    ((member target (map theorem-result found-proofs)) (findf (lambda (t) (equal? (theorem-result t) target)) found-proofs))
    ; Slucaj kade maksimalnata dlabocina e postignata
    ((> depth max-depth) #f)
    ; Vo sprotivno primenuva pravila vrz najdeni dokazi
    (else (letrec ([theorems (theorems-apply-rules prover found-proofs)]
                   [proofs-set (list->set (map theorem-result found-proofs))]
                   [theorems-set (list->set (map theorem-result theorems))])
            (if (equal? (set-union proofs-set theorems-set) proofs-set)
                #f ; Slucaj kade nema novi teoremi pronajdeni
                ; Vo sprotivno prodolzuva da bara
                (find-proof-iter prover target max-depth (merge-proofs found-proofs theorems) (+ 1 depth)))))))

; Pomosna funkcija
(define (find-proof prover target max-depth)
  (find-proof-iter prover target max-depth (theorem-prover-axioms prover) 0))
```

Последната функција `merge-proofs` спојува две листи на докази, притоа избегнувајќи дупликати:

```{language=racket}
(define (merge-proofs p1 p2)
  (remove-duplicates
    (append p1 p2)
    (lambda (t1 t2)
      (equal? (theorem-result t1) (theorem-result t2)))))
```

Еден пример за користење:

```{language=racket}
(define mu-rules
  (list
   (rule "One" (lambda (t p) (if (string-suffix? t "I") (string-append t "U") t)))
   (rule "Two" (lambda (t p)
                 (let ([matches (regexp-match #rx"M(.*)" t)])
                   (if (and (list? matches) (>= 2 (length matches)))
                       (string-append t (cadr matches))
                       t))))
   (rule "Three" (lambda (t p) (string-replace t "III" "U" #:all? #f)))
   (rule "Four" (lambda (t p) (string-replace t "UU" "" #:all? #f)))))

(define test-prover (theorem-prover (list (axiom "MI")) mu-rules))
(find-proof test-prover "MIUIU" 5)
```

Како резултат се добива `(theorem '("MI") (list (rule "One" #) (rule "Two" #)) "MIUIU")`, што вели дека за почетна теорема `MI` се применува правило `One`, па `Two` за да се постигне до бараниот заклучок.

## А.4. Пример: Програмирање со ограничувања

Во овој начин на програмирање, проблемот се претставува декларативно наместо да се пишува алгоритам за негово решавање. Слично беше постигнато и со дефинирање на `mu-rules` претходно, каде што проблемот беше моделиран преку листа на правила, но таму се користеа правила за да изменат теорема, додека во програмирање со ограничувања се користат правила за проверување релации.

Овој начин на програмирање е исто така познат како Constraint Programming, а математички се претставува преку тројката $(X, D, C)$ каде што:

- $X = \{ x_1, x_2, \ldots, x_n \}$ е множество на променливи
- $D = \{ d_1, d_2, \ldots, d_n \}$ е множество на домени (каде што на секое $x_i$ му се придружува $d_i$)
- $C = \{ c_1, c_2, \ldots, c_m \}$ е множество на ограничувања (constraints), каде што секое ограничување $c_k$ е пар $(S, R)$ за кој важи:
  - $S = (x_{i_1}, \ldots, x_{i_k})$ се променливи во $c_k$
  - $R \subseteq d_{i_1} \times \ldots \times d_{i_k}$ се $k$-торки што ја задоволуваат релацијата $c_k$

Истото претставено преку код:

```{language=racket}
(struct variable (name domain) #:prefab)
(struct constraint (variables formula) #:prefab)
(struct cpair (name value) #:prefab)
```

На пример, за моделот $x, y, z \in \{ 0, 1 \}, x + y = z$ важи:

- Променливи се: $x, y, z$
- Домените се $d_x = d_y = d_z = \{ 0, 1 \}$
- Единечно ограничување: $x + y = z$
- Решение на ограничувањето е парот $((x, y, z), \{(0, 0, 0), (1, 0, 1), (0, 1, 1)\})$.

Овој модел се претставува преку код на следниот начин:

```{language=racket}
(constraint (list (variable 'x '(0 1))
                  (variable 'y '(0 1))
                  (variable 'z '(0 1)))
            '(= (+ x y) z))
```

За решавање на овој проблем ќе биде искористен brute-force пристап кој ќе ги генерира сите можни парови од домените и ќе ги тестира врз ограничувањето.

```{language=racket}
(define (get-all-pairs c)
  (letrec ([vars (constraint-variables c)]
           [varnames (map variable-name vars)]
           [tuples (apply cartesian-product (map variable-domain vars))])
    (map (lambda (x) (map cpair varnames x)) tuples)))
```

Функцијата за наоѓање на решението се претставува на следниот начин:

```{language=racket}
(define (find-sat c)
  (define (go f ps)
    (cond ((null? ps) '())
          ((test-pair f (car ps)) (car ps))
          (else (go f (cdr ps)))))
  (letrec ([formula (constraint-formula c)]
           [pairs (get-all-pairs c)])
    (go formula pairs)))
```

Заедно со функцијата за тестирање:

```{language=racket}
(define (test-pair f p)
  (cond ((eq? p '()) (eval f))
        (else (let ([current-pair (car p)]
                    [remaining-pairs (cdr p)])
                (test-pair (subst (cpair-name current-pair)
                                  (cpair-value current-pair)
                                  f)
                           remaining-pairs)))))
```

На овој начин се покажа минимален систем за конструирање автоматски докази, сличен по природа со оној имплементиран во Dafny [18].

[^apa1]: Овој концепт се нарекува Quine, а се однесува на саморепродуцирачки програми, односно мета-програми ‒ програми што се враќаат сами себе по извршување.

[^apa2]: `define` соодветствува на апстракција, а повик (евалуација) соодветствува на апликација во ламбда калкулус системот.
