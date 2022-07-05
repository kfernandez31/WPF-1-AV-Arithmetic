(*
    Autor:     Kacper Kramarz-Fernandez (indeks: 429629, gr. IV)
    Reviewer:  Ryszard Markowski (gr. IV)
    Zadanie 1: Arytmetyka przybliżonych wartości

*)

open Float;;



(*(*(* TYPY *)*)*)
(* Typ reprezentujący:
- przedział zamknięty [a,b] (w szczególności nieliczbę [nan,nan]),
- dwa rozłączne przedziały otwarte [-inf,a]u[b,+inf] reprezentowane przez ich dopełnienie [a.b] do R,
*)
type wartosc = Przedzial of (float*float) | Dopelnienie of (float*float)
;;


(*(*(* FUNKCJE POMOCNICZE *)*)*)
(* Średnia arytmetyczna dwóch floatów *)
let srednia x y =
    (x +. y) /. 2.
;;


(*(*(* KONSTRUKTORY *)*)*)
(* Tworzy wartość z zerowym błędem: x +- 0% *)
let wartosc_dokladna x =
    Przedzial(x, x)
;;

(* Wartość reprezentująca (-inf,inf) *)
let prostaRzeczywista =
    Przedzial(neg_infinity, infinity)
;;

(* Wartość reprezentująca [nan,nan] *)
let nieliczba =
    Przedzial(nan, nan)
;;

(* Tworzy wartość z pewnym otoczeniem obustronnym *)
let wartosc_od_do x y =
    if (x <= y) then Przedzial (x,y) else Przedzial (y,x)
;;
    
(* Tworzy wartość uwzględniającą błąd p *)
let rec wartosc_dokladnosc x p = (* TODO: czy tu mogę dać rec? *)
    if (p >= 0.) then
        if (x >= 0.) then Przedzial((x *. ((100.-.p) /. 100.)), (x *. ((100.+.p) /. 100.)))
        else Przedzial((x *. ((100.+.p) /. 100.)), (x *. ((100.-.p) /. 100.)))
    else wartosc_dokladnosc x (-1. *. p)
;;




(*(*(* WERYFIKATORY *)*)*)
(* Sprawdza czy wartość x reprezentuje nieliczbę [nan,nan] *)
let czy_nieliczba x =
    match x with
    | Przedzial(a,b)   -> is_nan a || is_nan b
    | Dopelnienie(_,_) -> false 
;;

(* Sprawdza czy wartość x może być równa floatowi y *)
let in_wartosc x y =
    match x with
    | Przedzial(a,b)   -> if (czy_nieliczba x) then false else a <= y && y <= b
    | Dopelnienie(a,b) -> y <= a || b <= y
;;


(*(*(* SELEKTORY *)*)*)
(* Minimalna możliwa wartość dla x *)
let min_wartosc x = 
    match x with
    | Przedzial(a,b)   -> if (czy_nieliczba x) then nan else if (a <= b) then a else b
    | Dopelnienie(_,_) -> neg_infinity
;;

(* Maksymalna możliwa wartość dla x *)
let max_wartosc x =
    match x with
    | Przedzial(a,b)   -> if (czy_nieliczba x) then nan else if (a >= b) then a else b
    | Dopelnienie(_,_) -> infinity
;;

(* Średnia możliwa wartość dla x *)
let sr_wartosc x =
  match x with
  | Przedzial(a,b)    -> if (czy_nieliczba x) then nan else srednia a b
  | Dopelnienie (_,_) -> nan
;;


(*(*(* MODYFIKATORY *)*)*)
(* Suma dwóch przedziałów *)
let rec suma_prz w1 w2 = 
    if (czy_nieliczba w1 || czy_nieliczba w2) then nieliczba else 
    match (w1,w2) with
    | (Dopelnienie(a,b), Dopelnienie(c,d)) ->
        if (c >= b || d <= a) then Przedzial(neg_infinity,infinity)
        else if (a > c && b < d) then Dopelnienie(a,b)
        else if (a > c) then Dopelnienie(a,d)
        else if (b < d) then Dopelnienie(c,b)
        else Dopelnienie(c,d)
    | (Dopelnienie(a,b), Przedzial(c,d))   -> suma_prz (Przedzial(c,d)) (Dopelnienie(a,b))
    | (Przedzial(a,b), Dopelnienie(c,d))   ->
        if (a <= c && b >= d) then Przedzial (neg_infinity, infinity)
        else if (a <= c) then Dopelnienie (b,d)
        else if (b >= d) then Dopelnienie (a,c)
        else Dopelnienie (c,d)
    | (Przedzial (a,b), Przedzial (c,d))   ->
        if (b > d) then suma_prz (Przedzial(c,d)) (Przedzial(a,b))
        else if (b >= c) then
            if (a <= c) then (Przedzial (a,d))
            else (Przedzial (c,d))
        else (Dopelnienie(b,c)) 
;;

(* Operacja dodania dwóch wartości *)
let rec plus w1 w2 =
    if (czy_nieliczba w1 || czy_nieliczba w2) then nieliczba else 
    match (w1, w2) with
    | (Dopelnienie(a,b), Dopelnienie(c,d)) -> prostaRzeczywista
    | (Dopelnienie(a,b), Przedzial(c,d))   -> plus w2 w1
    | (Przedzial(a,b), Dopelnienie(c,d))   -> 
        if (b +. c >= a +. d) then 
            prostaRzeczywista
        else 
            Dopelnienie(c +. b, d +. a)
    | (Przedzial(a,b), Przedzial(c,d))     -> Przedzial(a +. c, b +. d)
;;

(* Operacja mnożenia dwóch wartości *)
let rec razy w1 w2 =
    if (czy_nieliczba w1 || czy_nieliczba w2) then nieliczba else
    let min_z_czterech a b c d    = min a (min b (min c d)) 
    in let max_z_czterech a b c d = max a (max b (max c d))
    in let mnoz x y =
        match (x, y) with
        | (a, 0.) when a = neg_infinity        -> neg_infinity 
        | (0., a) when a = neg_infinity        -> neg_infinity
        | (a, 0.) when a = infinity            -> infinity  
        | (0., a) when a = infinity            -> infinity   
        | (_,_) -> x *. y in 
        match (w1,w2) with
        | (Dopelnienie (a,b), Dopelnienie(c,d)) -> 
            let prz1 = razy (Przedzial(neg_infinity,a)) (Przedzial(neg_infinity,c))
            and prz2 = razy (Przedzial(neg_infinity,a)) (Przedzial(d,infinity))
            and prz3 = razy (Przedzial(b,infinity)) (Przedzial(neg_infinity,c))
            and prz4 = razy (Przedzial(b,infinity)) (Przedzial(d,infinity))
                in suma_prz (suma_prz prz1 prz2) (suma_prz prz3 prz4)
        | (Dopelnienie (a,b), Przedzial(c,d))   -> razy w2 w1
        | (Przedzial (a,b), Dopelnienie (c,d))  -> 
            let prz1 = razy (Przedzial(a,b)) (Przedzial(neg_infinity,c))
            and prz2 = razy (Przedzial(a,b)) (Przedzial(d,infinity))
                in suma_prz prz1 prz2
        | (Przedzial (a,b), Przedzial (c,d))    -> 
            if (w1 = wartosc_dokladna 0. || w2 = wartosc_dokladna 0.) then 
                wartosc_dokladna 0.
            else if (w1 = prostaRzeczywista || w2 = prostaRzeczywista) then 
                prostaRzeczywista
            else if ((a < 0. && b = 0. && c >= 0. && d = infinity) || (a >= 0. && b = infinity && c < 0. && d = 0.)) then
                Przedzial(neg_infinity,0.)
            else if ((a = neg_infinity && d = 0.) || (b = 0. && c = neg_infinity)) then 
                Przedzial(0.,infinity)
            else 
                Przedzial(min_z_czterech (mnoz a c)(mnoz a d)(mnoz b c)(mnoz b d), (max_z_czterech (mnoz a c)(mnoz a d)(mnoz b c)(mnoz b d)))
;;

(* Operacja odejmowania dwóch wartości *)
let minus w1 w2 =
    plus w1 (razy w2 (wartosc_dokladna (-1.)))
;;


(* Operacja dzielenia dwóch wartości *)
let rec podzielic w1 w2 =
    if (czy_nieliczba w1 || czy_nieliczba w2)      then nieliczba else
    match (w1,w2) with
    | (_,y) when y = wartosc_dokladna 0.   ->      nieliczba
    | (Dopelnienie(a,b), Dopelnienie(c,d)) ->
    let prz1 = podzielic (Przedzial(neg_infinity,a)) (Przedzial(neg_infinity,c))
    and prz2 = podzielic (Przedzial(neg_infinity,a)) (Przedzial(d,infinity))
    and prz3 = podzielic (Przedzial(b,infinity)) (Przedzial(neg_infinity,c))
    and prz4 = podzielic (Przedzial(b,infinity)) (Przedzial(d,infinity))
                                                   in suma_prz (suma_prz prz1 prz2) (suma_prz prz3 prz4)
    | (Przedzial(a,b), Dopelnienie(c,d))   ->
    let prz1 = podzielic w1 (Przedzial(neg_infinity,c))
    and prz2 = podzielic w1 (Przedzial(d,infinity))
                                                   in suma_prz prz1 prz2
    | (Dopelnienie(a,b), Przedzial(c,d))   ->
    let prz1 = podzielic (Przedzial(neg_infinity,a)) w2
    and prz2 = podzielic (Przedzial(b,infinity)) w2
                                                   in suma_prz prz1 prz2
    | (Przedzial(a,b), Przedzial(c,d))     ->
         if (a = 0. && b = 0.) then Przedzial(0.,0.)
    else if (a >=0. && c > 0.) then Przedzial(a /. d, b /. c)
    else if (a < 0. && b = 0. && c < 0. && d = 0.) then Przedzial(0.,infinity)
    else if (a < 0. && b = 0. && c = 0.)           then Przedzial(neg_infinity,0.)
    else if (a = 0. && c < 0.&& d = 0.)            then Przedzial(neg_infinity,0.)
    else if (a >= 0. && c < 0. && d = 0.)          then Przedzial(neg_infinity, a /. c)
    else if (a >=0. && c = 0.)                     then Przedzial(a /. d, infinity)
    else if (b < 0. && c < 0. && d = 0.)           then Przedzial(b /. c, infinity)
    else if (b <0. && c = 0.)                      then Przedzial(neg_infinity, b /. d)
    else if (b < 0. && d < 0.)                     then Przedzial(b /. c, a /. d)
    else if (a >= 0. && d < 0.)                    then Przedzial(b /. d, a /. c)
    else if (b < 0. && c >= 0.)                    then Przedzial(a /. c, b /. d)
    else if (a >= 0. && c < 0. && d >= 0.)         then Dopelnienie(a /. c, a /. d)
    else if (a < 0. && b >= 0. && c >= 0.)         then Przedzial(a /. c, b /. c)
    else if (b < 0. && c < 0. && d >= 0.)          then Dopelnienie(b /. d, b /. c)
    else if (a < 0. && b >= 0. && d < 0.)          then Przedzial(b /. d, a /. d)
    else                                           prostaRzeczywista
;;
