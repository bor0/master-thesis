# 1. Вовед

\pagenumbering{arabic}

Дизајнирањето коректни компјутерски системи е сложена и скапа задача и премногу често системот дава неточни или неочекувани резултати.

За софтверскиот дел, постојат неколку начини за справување со овој проблем. Во практиката, најчестиот пристап е да се напишат тестови, односно код кој го тестира оригиналниот код. Сепак, овие тестови можат да откриваат проблеми само во конкретни случаи[^ch1n1]. Еден од поретките (и поскапите) пристапи е да се напише формален доказ за коректност за даден код [15]. Ваквиот доказ за коректност е, всушност, математички доказ дека софтверот функционира според дадени спецификации. Со математички докази се покриваат сите можни случаи, а токму овие докази потврдуваат дека кодот го прави токму она што е наменето да го направи.

Виртуелната машина претставува емулација на компјутерски систем. Тие се погодни бидејќи со минимална инвестиција може да се емулираат хардверски системи, а притоа да нема потреба да се купува додатен хардвер. Преку програмскиот јазик Dafny ќе биде покажан пример за имплементација на виртуелна машина со користење на **Тјуринговите машини**, а **Хоаровата** логика ќе се искористи за да се докажат нејзините формални спецификации. Исто така, ќе бидат докажани неколку математички својства за нивните инструкциски множества.

За пример ќе биде искористена виртуелната машина CHIP-8, дизајнирана од Џозеф Вајсбекер во 1970-тите [17]. Оваа виртуелна машина е погодна како пример, бидејќи е едноставна за имплементација, но, истите идеи и концепти во овој магистерски труд може да се применат и на покомплексни чипови, како на пример Интеловите (Intel).

Овие концепти ќе бидат разгледани подетално во следните поглавја:

1. Во второто, третото и во четвртото поглавје ќе бидат претставени проблемот на истражувањето, појавата на истражувањето, хипотезата и очекуваните резултати.
1. Во петтото поглавје ќе бидат претставени математичките основи: формални системи, логика, теорија на множества, математички докази, теоремите на Гедел, Тјурингови машини, како и Хоаровата логика која овозможува да се вршат математички тврдења врз програми.
1. Во шестото поглавје ќе биде воведен програмскиот јазик **Dafny**.
1. Во седмото поглавје ќе бидат покажани актуелните истражувања за формална верификација и виртуелни машини.
1. Во осмото поглавје ќе бидат претставени виртуелни машини, како и понатамошни истражувања. За пример ќе се искористи едноставната виртуелна машина CHIP-8, каде што ќе биде претставена имплементацијата како и верификацијата на нејзиното инструкциско множество.
1. Во прилогот ќе се покаже поврзаноста меѓу обработка на симболи со дијагонализација, ќе биде претставен минимален систем за докажување својства, како и автоматски докажувач на теореми.

[^ch1n1]: Како што забележува познатиот математичар и програмер Едсгер Дејкстра, "тестирањето покажува присуство, а не отсуство на грешки".
