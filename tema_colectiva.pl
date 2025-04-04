implica(P,Q) :- not(P); Q.
echiv(P,Q) :- implica(P,Q), implica(Q,P).
xor(P,Q) :- P,not(Q) ; Q,not(P).
tripluegal(A,B,C) :- echiv(A,B), echiv(B,C), echiv(A,C).

difAB(A, B) :- A , not(B).
reunAB(A, B) :- A ; B.
intersAB(A, B) :- A , B.
implicatriplu(A, B, C, D) :- implica(A, B), implica(A, C), implica(A, D).


listaValBool(L) :- listaBool(L), write(L), nl.

listaBool([]).
listaBool([H|T]) :- member(H,[false,true]), listaBool(T).


/*
    A, B, C, D, T
    _a, _b, _c, _d, _t

    _a : x apartine lui A
    _b : x apartine lui B
    _c : x apartine lui C
    _d : x apartine lui D
    _t : x apartine lui T
*/

/* EXERCITIUL 1 */
rel1(_a,_b,_c) :- echiv((_a, (_b ; _c)), 
                        ((_a , _b) ; (_a , _c))).

demrel1 :- not((listaValBool([_a,_b,_c]),
            not(rel1(_a,_b,_c)))).
% ?- demrel1.

/* EXERCITIUL 2 */

reunEgal(_a, _b) :- echiv((_a ; _b), _b).
inclEgal(_a, _b) :- implica(_a, _b).
interEgal(_a, _b) :- echiv((_a , _b), _a).

rel2(_a, _b) :- echiv(
        echiv(reunEgal(_a, _b), inclEgal(_a, _b)), 
        echiv(inclEgal(_a, _b), interEgal(_a, _b))).

demrel2 :- not((listaValBool([_a,_b]),
            not(rel2(_a,_b)))).
% ?- demrel2.

/* EXERCITIUL 3 */

/* !!!!!!!!!! Poate fi schimbat*/
rel31(_a) :- echiv((_a ; false) , _a).
demrel31 :- not((listaValBool([_a]), not(rel31(_a)))).
% A reunit cu vid = vid ?- demrel31.

rel32(_a) :- echiv((_a , false) , false).
demrel32 :- not((listaValBool([_a]), not(rel32(_a)))).
% A intersectat cu vid = vid ?- demrel32.

rel33(_a) :- echiv((_a , true) , _a).
demrel33 :- not((listaValBool([_a]), not(rel33(_a)))).
% A diferenta cu vid = A  

rel34(_a) :- echiv((false , not(_a)) , false).
demrel34 :- not((listaValBool([_a]), not(rel34(_a)))).
% vid diferenta cu A = vid 

rel35(_a) :- rel33(_a) ; rel34(_a).
demrel35 :- not((listaValBool([_a]), not(rel35(_a)))).
% A diferenta simetrica cu vid = A  

/* EXERICITIUL 4 */

reunABVid(_a, _b) :- echiv((_a ; _b),false).
egalABVid(_a, _b) :- tripluegal(_a,_b,false).

rel41(_a, _b) :- echiv(reunABVid(_a, _b), 
                       egalABVid(_a, _b)).   
demrel41 :- not((listaValBool([_a,_b]),
            not(rel41(_a,_b)))).
% ?- demrel41.             

difABVid(_a, _b) :- echiv((_a , not(_b)), false).
rel42(_a, _b) :- echiv(difABVid(_a, _b), 
                       inclEgal(_a, _b)).
demrel42 :- not((listaValBool([_a,_b]),
            not(rel42(_a,_b)))).
% ?- demrel42.                           

difsimABVID(_a,_b) :- 
        echiv((difAB(_a,_b) ; difAB(_b,_a)), false).
rel43(_a, _b) :- echiv(difsimABVID(_a,_b),
                      echiv(_a, _b)).
demrel43 :- not((listaValBool([_a,_b]), 
            not(rel43(_a,_b)))).                      
% ?- demrel43.

/* EXERICITIUL 5 */
inclStrict(_a, _b) :- inclEgal(_a, _b), not(echiv(_a, _b)).
inclStrict2incl(_a, _b) :- inclEgal(_a, _b), not(inclEgal(_b, _a)).
inclStrictdif(_a, _b) :- inclEgal(_a, _b), not(difABVid(_b, _a)).
rel5(_a, _b) :- tripluegal(inclStrict(_a, _b), 
                            inclStrict2incl(_a, _b),
                            inclStrictdif(_a, _b)).
demrel5 :- not((listaValBool([_a,_b]),
            not(rel5(_a,_b)))).
% ?- demrel5.

/* EXERICITIUL 6 */
rel6(_a, _b) :- echiv(inclEgal(_a, _b), 
                     (inclStrict(_a, _b) ; echiv(_a, _b))).
demrel6 :- not((listaValBool([_a,_b]),
            not(rel6(_a,_b)))).
% ?- demrel6.

/* EXERICITIUL 7 */
rel71(_a, _b, _c) :- implica( (inclStrict(_a, _b), inclEgal(_b,_c)),                        
                              inclStrict(_a, _c)).
demrel71 :- not((listaValBool([_a,_b,_c]),
            not(rel71(_a,_b,_c)))).
% ?- demrel71.

rel72(_a, _b, _c) :- implica( (inclEgal(_a, _b), inclStrict(_b,_c)),                        
                              inclStrict(_a, _c)).
demrel72 :- not((listaValBool([_a,_b,_c]),
            not(rel72(_a,_b,_c)))).
% ?- demrel72.                              

rel73(_a, _b, _c) :- implica( (inclStrict(_a, _b), inclStrict(_b,_c)),                        
                              inclStrict(_a, _c)).
demrel73 :- not((listaValBool([_a,_b,_c]),
            not(rel73(_a,_b,_c)))).
% ?- demrel73.

/* EXERCITIUL 8 */
rel81right(_a, _b, _c) :- inclEgal((_a ; _c), (_b ; _c)).
rel81(_a, _b, _c) :- implica( inclEgal(_a, _b), 
                              rel81right(_a, _b, _c)).
demrel81 :- not((listaValBool([_a,_b,_c]),
            not(rel81(_a,_b,_c)))).
% ?- demrel81.

rel82right(_a, _b, _c) :- inclEgal(difAB(_a, _c), difAB(_b, _c)).
rel82(_a, _b, _c) :- implica( inclEgal(_a, _b), 
                              rel82right(_a, _b, _c)).
demrel82 :- not((listaValBool([_a,_b,_c]),
            not(rel82(_a,_b,_c)))).
% ?- demrel82.

rel83right(_a, _b, _c) :- inclEgal(difAB(_c, _b), difAB(_c, _a)).
rel83(_a, _b, _c) :- implica( inclEgal(_a, _b), 
                              rel83right(_a, _b, _c)).
demrel83 :- not((listaValBool([_a,_b,_c]),
            not(rel83(_a,_b,_c)))).
% ?- demrel83.

/* EXERCITIUL 9 */

rel9left(_a, _b, _c, _d) :- interEgal(_a, _b) , interEgal(_c, _d).
rel9right1(_a, _b, _c, _d) :- inclEgal(reunAB(_a, _c), reunAB(_b, _d)).
rel9right2(_a, _b, _c, _d) :- inclEgal(intersAB(_a, _c), intersAB(_b, _d)).
rel9right3(_a, _b, _c, _d) :- inclEgal(difAB(_a, _d), difAB(_b, _c)).
rel9(_a, _b, _c, _d) :- implicatriplu(rel9left(_a, _b, _c, _d), 
                                    rel9right1(_a, _b, _c, _d),
                                    rel9right2(_a, _b, _c, _d),
                                    rel9right3(_a, _b, _c, _d)).
demrel9 :- not((listaValBool([_a,_b,_c,_d]),
            not(rel9(_a,_b,_c,_d)))).
% ?- demrel9.

/* EXERCITIUL 10 */ 
rel101(_a, _b) :- inclEgal(difAB(_a, _b), _a). 
demrel101 :- not((listaValBool([_a,_b]),
            not(rel101(_a,_b)))).
% ?- demrel101.
% A \ B inclus egal A  

rel102(_a, _b) :- echiv(intersAB(_a, difAB(_a, _b)),
                        difAB(_a, _b)).
demrel102 :- not((listaValBool([_a,_b]),
            not(rel102(_a,_b)))).
% ?- demrel102.
% A intersectat cu A \ B = A \ B

rel103(_a, _b) :- echiv(intersAB(_a, difAB(_b, _a)), false).
demrel103 :- not((listaValBool([_a,_b]),
            not(rel103(_a,_b)))).
% ?- demrel103.
% A intersectat cu B \ A = vid

/* EXERCITIUL 11 */
intersABVid(_a, _b) :- echiv(intersAB(_a, _b), false). 
difAEgalB(_a, _b) :- echiv(difAB(_a, _b), _a).
rel11(_a, _b) :- tripluegal(intersABVid(_a, _b), 
                            difAEgalB(_a, _b),
                            difAEgalB(_b, _a)).
demrel11 :- not((listaValBool([_a,_b]),
            not(rel11(_a,_b)))).
% ?- demrel11.

/* EXERCITIUL 12 */
rel121(_a, _b) :- echiv(inclEgal(_a, _b), 
                        inclEgal(not(_b), not(_a))).
demrel121 :- not((listaValBool([_a,_b]),
            not(rel121(_a,_b)))).
% ?- demrel121.
% A inclus egal B <=> A complement inclus egal B complement

rel122(_a, _b) :- echiv( echiv(_a, _b), 
                        echiv(not(_b), not(_a))).
demrel122 :- not((listaValBool([_a,_b]),
            not(rel122(_a,_b)))).
% ?- demrel122.
% A = B <=> A complement = B complement

rel123(_a, _b) :- echiv( inclStrict(_a, _b), 
                        inclStrict(not(_b), not(_a))).
demrel123 :- not((listaValBool([_a,_b]),
            not(rel123(_a,_b)))).
% ?- demrel123.
% A inclus strict B <=> A complement inclus strict B complement

/* EXERCITIUL 13 */

rel131(_a, _b) :- tripluegal(intersABVid(_a, _b), inclEgal(_a, not(_b)), 
                           inclEgal(_b, not(_a))).
demrel131 :- not((listaValBool([_a,_b]),
            not(rel131(_a,_b)))).
% ?- demrel131.

rel132left(_a, _b, _t) :- echiv(reunAB((_a , _t), (_b , _t)), _t).
rel132(_a, _b, _t) :- tripluegal(rel132left(_a, _b, _t), 
                                inclEgal((not(_b) , _t), (_a , _t)),
                                inclEgal((not(_a) , _t), (_b , _t))).
demrel132 :- not((listaValBool([_a,_b,_t]),
            not(rel132(_a,_b,_t)))).
% ?- demrel132.

/* EXERCITIUL 14 */
difSim(_a, _b) :- reunAB(difAB(_a, _b), difAB(_b, _a)).
rel14(_a, _b) :- echiv(difSim(_a, _b), 
                       difAB(reunAB(_a, _b), 
                             intersAB(_a, _b))).
demrel14 :- not((listaValBool([_a,_b]),
            not(rel14(_a,_b)))).
% ?- demrel14.
% A diferenta simetrica B = A reunita cu B - A intersectat cu B