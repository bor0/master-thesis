# 8. Верификација на виртуелни машини

Компјутерските системи содржат сложени хардверски компоненти [16]. Некои од тие компоненти се битови, регистри, меморија, итн. Сите тие се поврзуваат преку електрично коло, а со инструкциите (командите) дефинирани во централниот процесор се менува состојбата на компонентите. Теориски, логиката на овие компоненти се темели на Булова алгебра, која е слична со логиката објаснета во 5.2.1, со тоа што вредностите се 1 и 0 наместо $\top$ и $\bot$.

Докажувањето на коректноста на физички компјутерски системи е премногу скапа задача. Вообичаено е тоа првично да се направи на т.н. **емулирани системи**, односно се врши емулација на хардверот каде што тој се мапира во софтвер, па се тестира емулацијата, па потоа се тестира хардверот физички. Виртуелните машини претставуваат емулација на компјутерски систем.

Компјутерската програма, всушност, претставува низа на инструкции, а како што беше покажано, со Тјуринговите машини, овие програми може да се претстават како математички модели. Потоа, со Хоаровата логика може да се докажат математички својства за овие програми.

Следува пример-код од Интеловиот процесор:

```
mov eax, 1234
mov ecx, 1
mov dword [eax], ecx
```

Овој код ја нагодува вредноста на регистарот `eax` на 1234, а потоа вредноста на регистарот `ecx` на 1. Со третата команда, се запишува во адресата што е содржана во `eax`, односно, целиот код ја нагодува вредноста на адресата 1234 да изнесува 1. Меѓутоа, Интеловиот процесор е многу сложен за разгледување, па затоа ќе биде имплементирана виртуелна машина со поедноставна архитектура, која содржи помалку инструкции.

Во ова поглавје ќе биде претставена виртуелнатата машина CHIP-8, нејзина имплементација како и верификација на неколку својства.

## 8.1. CHIP-8 виртуелна машина

CHIP-8 е виртуелна машина создадена во 1970-тите, првично наменета за компјутерски игри [17]. Таа е позната по едноставниот дизајн, а се содржи од:

1. Шеснаесет 8-битни регистри обележани `V0` до `VF`, каде што `VF` некогаш служи како знак за пренос
1. Адресен регистар `I`
1. Програмски бројач `PC`
1. Покажувач кон стек `SP`
1. Меморија со должина од 3584 бајти
1. Стек со нивоа на вгнездување
1. Резолуција со должина 64x32 пиксели
1. Тајмери за звук и за одложување

### 8.1.1. Детали за имплементацијата

Постојат неколку имплементации на оваа виртуелна машина, а една таква е во C [14]. Од тој код ќе биде покажана нејзината структура.

```c
struct vm {
    struct {
        uint8_t v[16];
        uint16_t I;
        uint16_t PC;
        uint16_t SP;
    } registers;
    uint8_t memory[0x0FFF];
    uint16_t stack[16];
    uint8_t halt;
    uint8_t display[2048];
    uint8_t key[16];
    uint8_t sound_timer, delay_timer;
};
```

Покрај оваа структура, следува функцијата за иницијализација, која ќе ја прочита програмата што треба да се изврши од податокот `f` и него ќе го вметне во меморијата на виртуелната машина.

```c
void vm_init(struct vm *VM, FILE *t) {
    memset(VM, '\0', sizeof(struct vm));
    VM->registers.PC = 0x200;

    i = 0;

    while (!feof(t) && i < 0xFFF - 0x200) {
        int fH, fL;

        fH = fgetc(t);
        if (fH == -1) break;
        VM->memory[VM->registers.PC + i] = fH;

        fL = fgetc(t);
        if (fL == -1) break;
        VM->memory[VM->registers.PC + i + 1] = fL;

        i += 2;
    }
}
```

Откако програмата ќе се вметне во меморија, се започнува со читање на инструкцијата од тековниот покажувач, па таа се извршува, па потоа тековниот покажувач се зголемува за да се прејде кон извршување на наредната инструкција, и така во циклус сѐ додека програмата не заврши.

Кодот за извршување инструкции е претставен на следниот начин:

\newpage{}

```c
void parse_opcode(struct vm *VM, uint16_t opcode) {
    switch (opcode) {
    case 0x00E0:
        /* Clears the screen. */
        memset(VM->display, 0, sizeof(VM->display));
        break;
//...
    }
```

### 8.1.2. Пример-програма

Една пример-програма е како на слика \ref{primer-chip8}, каде што за неа е зададен и hex-кодот.

![Пример-програма во CHIP-8\label{primer-chip8}](images/primer-chip8.png){ width=650px }

```
0000000 12 2c 47 52 45 45 54 2e 41 53 4d 2c 20 43 6f 70
0000010 79 72 69 67 68 74 20 32 30 31 34 20 42 6f 72 6f
0000020 20 53 69 74 6e 69 6b 6f 76 73 6b 69 61 00 62 05
0000030 a2 af d1 25 61 06 62 05 a2 b4 d1 25 61 0c 62 05
0000040 a2 b9 d1 25 61 12 62 05 a2 be d1 25 61 1e 62 05
0000050 a2 aa d1 25 61 24 62 05 a2 9b d1 25 61 2a 62 05
0000060 a2 be d1 25 61 30 62 05 a2 a5 d1 25 61 05 62 0f
0000070 a2 a0 d1 25 61 0f 62 0f a2 be d1 25 61 19 62 0f
0000080 a2 9b d1 25 61 23 62 0f a2 be d1 25 61 2d 62 0f
0000090 a2 96 d1 25 12 94 08 24 04 24 08 1c 14 1e 12 12
00000a0 3c 24 38 24 3c 36 2a 2a 22 22 1c 10 1c 10 10 14
00000b0 14 1c 14 14 1c 14 1c 14 14 10 10 10 10 1c 1c 14
00000c0 14 14 1c
00000c3
```

Односно, дел од асемблерскиот код:

```
jump    start
.ascii  "GREET.ASM, Copyright 2014 Boro Sitnikovski"
start:
HALO:
    load    v1, 0
    load    v2, 5
    load    i, l_H
    draw    v1, v2, 5
    load    v1, 6
    load    v2, 5
    load    i, l_A
    draw    v1, v2, 5
    load    v1, 12
    load    v2, 5
    load    i, l_L
    draw    v1, v2, 5
    load    v1, 18
    load    v2, 5
    load    i, l_O
    draw    v1, v2, 5
FROM: ;...
```

\newpage{}

### 8.1.3. Инструкциско множество

CHIP-8 има 35 инструкции, од кои сите се со должина од 2 бајти. Во имплементацијата ќе биде имплементирано мало подмножество на виртуелната машина, како и на инструкциите, што ќе служи за докажување на тезата.

За комплетност, целосната листа на инструкциите е дадена во следната табела [14].

| Инструкција | Опис                                                     |
| ----------- | -------------------------------------------------------- |
| `00E0`      | Го чисти екранот. |
| `0NNN`      | Повик до рутина на машински код на адреса `NNN`. |
| `2NNN`      | Повик до субрутина на `NNN`. |
| `00EE`      | Враќа назад од субрутина. |
| `1NNN`      | Скок до адреса `NNN`. |
| `3XNN`      | Ја прескокнува следната инструкција ако `VX` е еднакво на `NN`. |
| `4XNN`      | Ја прескокнува следната инструкција ако `VX` не е еднакво на `NN`. |
| `5XY0`      | Ја прескокнува следната инструкција ако `VX` е еднакво на `VY`. |
| `9XY0`      | Ја прескокнува следната инструкција ако `VX` не е еднакво на VY. |
| `EX9E`      | Ја прескокнува следната инструкција ако копчето во `VX` е стиснато. |
| `EXA1`      | Ја прескокнува следната инструкција ако копчето во `VX` не е стиснато. |
| `6XNN`      | Го нагодува `VX` на `NN`. |
| `8XY0`      | Го нагодува `VX` на вредноста на `VY`. |
| `8XY1`      | Го нагодува `VX` на `VX OR VY`. |
| `8XY2`      | Го нагодува `VX` на `VX AND VY`. |
| `8XY3`      | Го нагодува `VX` на `VX XOR VY`. |
| `8XY7`      | Го нагодува `VX` на `VY - VX`. `VF` се нагодува на 0 кога има позајмување, а на 1 во спротивно. |
| `ANNN`      | Го нагодува тековниот покажувач на адресата `NNN`. |
| `BNNN`      | Го нагодува тековниот покажувач на адресата `NNN + V0`. |
| `CXNN`      | Го нагодува `VX` на `NN` AND случаен број. |
| `FX07`      | Го нагодува `VX` на вредноста на тајмерот за одложување. |
| `FX15`      | Го нагодува тајмерот на одложување на `VX`. |
| `FX18`      | Го нагодува тајмерот на звук на `VX`. |
| `FX29`      | Го нагодува I на локацијата на графиката за знакот во `VX`. |
| `8XY6`      | Го зачувува најмалку значајниот бит од VX во VF, а потоа врши поместување надесно на `VX`. |
| `8XYE`      | Го зачувува најмногу значајниот бит од VX во VF, а потоа врши поместување налево на `VX`. |
| `FX65`      | Ги нагодува регистрите `V0` до `VX` (вклучувајќи `VX`) со вредности од меморијата, започнувајќи на адреса `I`. |
| `FX55`      | Ги зачувува вредностите од регистрите `V0` до `VX` (вклучувајќи `VX`) на меморијата, почнувајќи од адреса `I`. |
| `7XNN`      | Додава `NN` на `VX`, а знакот за пренос не се менува. |
| `8XY4`      | Додава `VY` на `VX`. `VF` се нагодува на 1 кога има пренос, а на 0 во спротивно. |
| `FX1E`      | Додава `VX` на `I`. `VF` не се менува. |
| `8XY5`      | `VY` се одзема од `VX`. `VF` се нагодува на 0 кога има позајмување, а на 1 во спротивно. |
| `DXYN`      | Исцртува графика на координатата (`VX`, `VY`) со должина од 8 пиксели и висина од `N` пиксели. Секој ред на 8 пиксели се чита почнувајќи од мемориската локација `I`. |
| `FX0A`      | Се чека стискање на копче, а потоа се зачувува во `VX`. |
| `FX33`      | Зачувува BCD (бинарно кодирање) во `VX`. |

  : Листа на CHIP-8 инструкции

## 8.2. Имплементација на CHIP-8 во Dafny

Во овој дел ќе биде претставена имплементацијата на CHIP-8 во Dafny, заедно со процесирањето на некои одредени инструкции. За поедноставна имплементација, ќе бидат изземени деловите за цртање на графика и звук.

Се започнува со дефинирање на класата `VM`, која е во согласност со компонентите дефинирани во 8.1.

```{language=dafny}
class VM
{
    var v: array<bv8>;
    var I: bv16;
    var PC: bv16;
    var SP: bv16;
    var memory: array<bv8>;
    var stack: array<bv16>;
    var sound_timer: bv8;
    var halt: bv8;
}
```

Потоа во истата класа се дефинира предикатот за валидност:

```{language=dafny}
    predicate Valid()
      reads this
    {
        v.Length == 16
        && 0 <= SP as int < stack.Length
        && memory.Length == 0x0FFF
        && stack.Length == 16
    }
```

Заедно со конструкторот за иницијализација на податоците на процесорот:

\newpage{}

```{language=dafny}
    constructor Init()
      ensures Valid()
    {
        v := new bv8[16];
        I := 0;
        PC := 0x200;
        SP := 0;
        memory := new bv8[0x0FFF];
        stack := new bv16[16];
        halt := 0;
    }
```

Со следниот код ќе биде прикажан едноставен пример со којшто се тврди дека која било инструкција (освен скок) го зголемува програмскиот бројач за 2. Се користи клучниот збор `modifies` за да му се каже на Dafny дека одреден параметар се менува од методот.

```{language=dafny}
method parse_opcode(vm: VM, opcode: bv16)
  modifies vm
  ensures opcode & 0xF000 != 0x1000 ==> vm.PC == old(vm.PC) + 2
  ensures opcode & 0xF000 == 0x1000 ==> vm.PC == opcode & 0x0FFF + 2
{
    if opcode & 0xF000 == 0x1000
    {
        vm.PC := opcode & 0x0FFF;
    }
    else if opcode & 0xF000 == 0xA000
    {
        vm.I := opcode & 0x0FFF;
    }
    vm.PC := vm.PC + 2;
}
```

\newpage{}

Додека со следниот код се иницира виртуелната машина и се вршат неколку тврдења.

```{language=dafny}
method Main()
{
    var vm := new VM.Init();
    parse_opcode(vm, 0x1123);
    print vm.PC, "\n"; // 293
    assert vm.PC == 293;
}
```

Со овие дефиниции беше зададена едноставна имплементација на CHIP-8 и може да се прејде кон нејзина верификација.

## 8.3. Верификација на одредени својства во Dafny

Во овој дел ќе бидат прикажани неколку примери за верификација на имплементацијата од 8.2.

По примерите ќе може да се забележи дека доколку се разгледува само делот за верификација, а се изземе делот за имплементација, тогаш полесно е системот да се анализира со цел да се подобри.

### 8.3.1. Jump (скок) не влијае на покажувачот на стек

Во овој дел ќе биде покажано дека инструкцијата `1NNN` не го менува покажувачот на стек, иако потенцијално може да го смени програмскиот бројач.

```{language=dafny}
method parse_opcode_jump(vm: VM, opcode: bv16)
  modifies vm
  ensures opcode & 0xF000 == 0x1000 ==> vm.SP == old(vm.SP)
{
    if opcode & 0xF000 == 0x1000
    {
        vm.PC := opcode & 0x0FFF;
    }

    vm.PC := vm.PC + 2;
}
```

Со користење на вградената функција `old()` може да се пристапи до претходната вредност на параметарот. Односно, `vm.SP == old(vm.SP)` означува дека покажувачот на стек останува ист по извршување на кодот во имплементацијата.

Како што беше споменато, сложеноста на имплементацијата може да се изземе и само да се фокусира на верификацијата, односно следниот код, сам по себе, кажува доволно за тоа што прави еден метод:

```{language=dafny}
method parse_opcode_jump(vm: VM, opcode: bv16)
  modifies vm
  ensures opcode & 0xF000 == 0x1000 ==> vm.SP == old(vm.SP)
```

\newpage{}

### 8.3.2. Инструкцијата `FX18` го нагодува тајмерот за звук

Во овој дел ќе се докаже дека тајмерот за звук се менува со дадената инструкција.

```{language=dafny}
method parse_opcode_timer_try(vm: VM, opcode: bv16)
{
    if opcode & 0xF0FF == 0xF018
    {
        vm.sound_timer := vm.v[(opcode & 0x0F00) >> 8];
    }
}
```

Првата грешка што се добива е тоа дека имплементацијата прави измена на виртуелната машина. За да се надмине таа грешка, се додава `modifies vm` во делот на верификацијата. Следната грешка што ќе се добие е `index out of range`. За да се надмине оваа грешка, се користи предусловот `requires vm.Valid()`, односно дека регистрите се иницијализирани.

Сега Dafny не враќа грешки, меѓутоа треба да се одбере својство што ќе важи за имплементацијата. Дополнително, од својството треба да е очигледно што прави методот без да се гледа имплементацијата. Едно такво својство е: доколку се проследи инструкција во валидни граници, тогаш звучниот тајмер ќе биде изменет.

Целосниот код за овој доказ е претставен следно:

```{language=dafny}
method parse_opcode_timer(vm: VM, opcode: bv16)
  modifies vm
  requires vm.Valid()
  ensures opcode & 0xF0FF == 0xF018
  && 0 <= ((opcode & 0x0F00) >> 8) as int < vm.v.Length
  ==> vm.sound_timer == vm.v[((opcode & 0x0F00) >> 8) as int]
{
    if opcode & 0xF0FF == 0xF018
    {
        vm.sound_timer := vm.v[(opcode & 0x0F00) >> 8];
    }
}
```

\newpage{}

### 8.3.3. Решавање грешка во инструкцијата `FX65`

Во овој дел ќе се покаже како може да се најде и да се поправи грешка при имплементација на инструкција.

```{language=dafny}
method parse_opcode_registers(vm: VM, opcode: bv16)
  requires vm.Valid()
  modifies vm`I, vm.v
{
    var i: int := 0;
    var bound := ((opcode & 0x0F00) >> 8) as int;

    if opcode & 0xF0FF == 0xF065
    {
        while i < bound
        {
            vm.v[i] := vm.memory[vm.I];
            i := i + 1;
            vm.I := vm.I + 1;
        }
    }
}
```

Во делот `modifies`, за примитивни типови на членови на класата се користи ``vm`x``, а за сложени типови се користи `vm.x`. Дополнително, со синтаксата `i as int` се трансформира типот на `i` во цел број за да може да се пристапи до индексот.

Dafny автоматски го детектира `decreases` делот за циклусот:

```{language=dafny}
decreases bound - i
```

Меѓутоа, Dafny враќа грешка `index out of range` за командата на линија 12. Тоа што не е очигледно во ваквиот циклус е дека алгоритамот може да излезе од границите, доколку `vm.I` се зголеми за повеќепати од должината на меморијата на виртуелната машина.

\newpage{}

Проблемот се решава со менување на условот на циклусот во:

```{language=dafny}
while i < bound && vm.I as int < vm.memory.Length
```

Но, доколку се изврши повик до функцијата како на следниот начин, Dafny ќе врати грешка.

```{language=dafny}
method Main()
{
    var vm := new VM.Init();
    print vm.I;
    parse_opcode_registers(vm, 0xF165);
    print vm.I;
    parse_opcode_registers(vm, 0xF165);
    print vm.I;
}
```

Причината за тоа е дека Dafny не знае дека `vm.v` доаѓа од `Init` конструкторот, бидејќи не е назначено во делот на верификацијата. Претходно овој проблем не се појави бидејќи не се референцираа членови на класата што алоцираат дополнителна меморија со користење на клучниот збор `new`, па Dafny можеше да заклучи од каде доаѓаат тие објекти, додека за низите беше алоцирана меморија. Поради ова, во делот на спецификација ќе се искористи вградената функција `fresh(r)`, која означува дека вратената вредност `r` ќе биде, всушност, новокреирана вредност.

Со додавање на следниот код во конструкторот на `VM`, проблемот се решава:

```{language=dafny}
ensures fresh(v) && fresh(memory) && fresh(stack)
```

\newpage{}

### 8.3.4. `pop` е инверзија на `push`

Во следниот дел ќе биде претставена имплементацијата за работа со податочната структура стек, односно командите `push` и `pop`, кои претставуваат повик до функција и враќање од неа, соодветно.

Најпрво, ќе биде проширена виртуелната машина со додавање на следниот copy конструктор:

```{language=dafny}
    constructor Copy(vm_old: VM)
      requires vm_old.Valid()
      ensures Valid()
      ensures fresh(stack) && fresh(memory) && fresh(v)
    {
        var x := copy_array(vm_old.v);
        v := x;
        I := vm_old.I;
        PC := vm_old.PC;
        SP := vm_old.SP;
        var y := copy_array(vm_old.memory);
        memory := y;
        var z := copy_array(vm_old.stack);
        stack := z;
        halt := vm_old.halt;
    }
```

Овој конструктор го користи помошниот метод `copy_array`, кој се претставува на следниот начин:

```{language=dafny}
method copy_array<T>(src: array<T>) returns (r: array<T>)
  ensures r.Length == src.Length
  ensures fresh(r)
{
    r := new T[src.Length](i requires 0 <= i < src.Length reads src => src[i]);
}
```

Овој метод прави 1:1 копија на низи, без поместување. Ова е потребно за да му се потврди на Dafny дека не се модифицира постоечката вредност (со користење на `fresh`).

Овие методи за копирање ќе бидат потребни бидејќи начинот на дефинирање на следната инструкција ќе биде различен од претходно. Наместо да се модифицира постоечка виртуелна машина, ќе се враќа целосно нова, со ажурирани вредности. Причината за ова е да се покаже различен начин на компутација, во кој се избегнува мутација (измена на постоечките вредности).

Следно ќе биде претставен методот за парсирање на командите.

```{language=dafny}
method parse_opcode_stack(vm: VM, opcode: bv16) returns (vm_new: VM)
  requires vm.Valid()
  requires 0 <= vm.SP as int < vm.stack.Length
  ensures opcode & 0xF000 == 0x2000 && vm_new.halt != 1 ==> vm_new.SP == vm.SP + 1
  ensures opcode == 0x00EE && vm_new.halt != 1 ==> vm_new.SP == vm.SP - 1
  ensures fresh(vm_new) && vm_new.Valid()
{
    vm_new := new VM.Copy(vm);
    if opcode & 0xF000 == 0x2000
    {
        if vm.SP as int >= vm.stack.Length - 1
        {
            vm_new.halt := 1;
            return;
        }
        vm_new.stack[vm.SP as int] := vm_new.PC;
        vm_new.SP := vm.SP + 1;
        vm_new.PC := opcode & 0x0FFF;
    }
    if opcode == 0x00EE
    {
        if vm.SP < 1
        {
            vm_new.halt := 1;
            return;
        }
        vm_new.PC := vm.stack[vm.SP];
        vm_new.SP := vm.SP - 1;
    }
}
```

Линиите 9-19 претставуваат `push` (`call`), а линиите 20-29 претставуваат `pop` (`return`). Следно ќе се докаже дека `pop` е инверзија на `push`, односно својството `push(pop(x)) == x`:

```{language=dafny}
method Main()
{
    var vm := new VM.Init();
    var vm_2 := parse_opcode_stack(vm, 0x2020);
    assert vm_2.halt != 1 ==> vm_2.SP == vm.SP + 1;
    var vm_3 := parse_opcode_stack(vm_2, 0x00EE);
    assert vm_3.halt != 1 ==> vm_3.SP == vm_2.SP - 1;
    assert vm_3.halt != 1 && vm_2.halt != 1 ==> vm_3.SP == vm.SP;
}
```

Под претпоставка дека виртуелната машина во ниту еден момент не запрела поради грешка, повик кон `0x2020` го зголемува `SP` за еден, а повик кон `0x00EE` го намалува зголемениот `SP`, па така вредноста на `SP` останува иста. Доколку се обрне внимание само на делот на верификација од `parse_opcode_stack`, аргументот од претходната реченица е очигледен:

```{language=dafny}
method parse_opcode_stack(vm: VM, opcode: bv16) returns (vm_new: VM)
  ...
  ensures opcode & 0xF000 == 0x2000 && vm_new.halt != 1 ==> vm_new.SP == vm.SP + 1
  ensures opcode == 0x00EE && vm_new.halt != 1 ==> vm_new.SP == vm.SP - 1
```

Овој начин на анализа и верифицирање е мошне моќен и дава увид во внатрешното функционирање на виртуелната машина.

## 8.4. Ограничувања

Инструкциите во инструкциските множества може да се групираат на:

- Аритметички ‒ инструкции што вршат аритметички операции;
- Логички ‒ инструкции што вршат логички операции;
- I/O ‒ инструкции што вршат операции со влезни или излезни уреди.

Во претходниот дел беше покажано како може да се верификуваат аритметички и логички инструкции. Но, верификацијата на инструкции што вршат операции со влезно-излезни уреди, а и поопшто, верификацијата на I/O ефекти, останува дел кој е предизвик за верификација.

Во програмирањето, I/O генерално претставува проблем, како за верификација така и за софтверски тестови.

Еден начин да се претстави I/O пресметка е со користење **монади** [36]. Односно, монад е алгебарска структура што на еден начин опфаќа компјутерска пресметка. Програмскиот јазик Haskell имплементира I/O преку користење монади, а во функционалното програмирање, верификацијата на I/O преку монади е истражена во [37].

Во делот на императивното програмирање, односно, поконкретно во Dafny, постои начин да се имплементира поддршка за I/O, со тоа што се пишуваат методи со спецификација во Dafny, а самата имплементација на конкретната I/O операција е во C# [38]. Иако е возможно, овој начин е непрактичен, односно останува поле што може да се истражи и да се подобри дополнително.

Покрај I/O, друг предизвик што се појавува при верификацијата е точно да се дефинираат формалните спецификации за софтвер. Бидејќи претежно развојот на софтвер во денешно време се врши итеративно и брзо, ова не секогаш е лесно поради тоа што спецификацијата е долготрајна задача. Покрај тоа, спецификацијата се темели врз конкретна имплементација, а со секоја итерација се менуваат делови од имплементацијата.

Поконкретно, истражувањето во [35] претставува добар пресек за техники, како и модели и алатки што се користат при формална верификација на софтвер.
