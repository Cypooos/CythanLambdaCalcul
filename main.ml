(*
  ----- INFORMATIONS -----

  Toute les fonctions de conversions sont inutiles, elle permettent juste de plus facilement
  créé / transformer des objets ocaml en objets de lambda calcul (afficher, convertir et débugger)
  
  En dehors de ces fonctions spécifique il est à noter que la composition et la création de 
  nouvelle fonctions (on lie une variable) sont les seules opérations utillisé. C'est le fondement du
  lambda-calcul : réduction (composition / appel) et création de fonction.

  Fichier basé sur https://fr.wikipedia.org/wiki/Lambda-calcul, avec quelques modifications sur la
  définition d'un couple car c'est plus pratique.

  Il est aussi à noté que ici le lambda calcul est simplement typé (merci ocaml) (je crois), donc la
  calculabilité est moindre que le lambda calcul classique

*)

(* La fonction identité !!! :D *)
let id x = x;;


(*
  ----- LES BOOLEENS -----
*)

(* En français car true / false existe déjà comme mot-clef d'Ocaml *)
let vrai a b = a;;
let faux a b = b;;

(* ifthenelse = λbuv.b u v *)
let ifthenelse b u v = b u v;;

(* Vérifions que cela fonctionne ! *)
print_int (ifthenelse vrai 1 2);; (* Affiche 1 *)
print_int (ifthenelse faux 1 2);; (* Affiche 2 *) 




(*
  ----- LES ENTIERS -----
*)

let zero = (fun f x -> x);;
let succ n = (fun f x -> f (n f x));;
let iter n base fct = n fct base;;

(* Fonctions de conversion / débuggage *)
let lint_to_int n = n (fun x -> x+1) 0;;
let rec int_to_lint = function
  | 0 -> zero
  | n -> succ (int_to_lint (n-1)) 
let prnt_lint n = Printf.sprintf "%d\n" (lint_to_int n);; 

(*Pour éviter l'apparition de weak du à une fonction sans argument, on prend n comme argument.
Cela ne change rien au type construit final, mais permet le débuggage! Ocaml est bizarre...
*) 
let one n = (succ zero) n;;
let two n = (zero |> succ |> succ) n;;
let three n = (zero |> succ |> succ |> succ) n;;

(* executer ce code sans prendre n précédemment aurai comme effet de lier tout les 'weak' 
présents avec des ints *)
(* Vérifions que cela fonctionne ! *)
prnt_lint zero ;;
prnt_lint one ;;
prnt_lint two ;;

(* Test si n=0, si oui retourne a sinon b *)
let ifzerothen n a b = n (fun x -> b) a;;


(* Vérifions que cela fonctionne ! *)
print_int (ifzerothen zero 1 0);;
print_int (ifzerothen one 1 0);;
print_int (ifzerothen two 1 0);;



(*
  ----- LES COUPLES ET PREDECESSEUR(a) -----
*)


(* On utillisera vrai pour couple.(0) et faux pour couple.(1) *)
let couple a b = (fun x -> ifthenelse x a b)

(* Pour éviter les weaks, on prend n. Définition de constantes utiles *)
let i1 n = vrai n;;
let i2 n = faux n;;
let empty n = (couple zero zero) n;;
let c1_0 n = (couple (zero |> succ) zero) n ;;

(* Conversion / print *)
let lcpl_to_cpl cpl = (cpl i1, cpl i2);;
let prnt_lcpl cpl = Printf.sprintf "(%d, %d)\n" (lint_to_int (cpl i1)) (lint_to_int (cpl i2));;

(* Important pour la fonction prédécesseur => prend un couple (a,b) et renvoie (b, b+1) *)
let decale_add cpl = couple (cpl i2) (succ (cpl i2));; 

(* YES! *)
let pred n = (iter n empty decale_add) i1;;

(* Sans n, executer ce code aurai lié tout les 'weak' présents avec des ints *)
(* Vérifions que cela fonctionne ! *)
(couple (zero |> succ) zero) i1 |> lint_to_int;; (* couple (1,0) *)
prnt_lcpl c1_0;;
prnt_lcpl (couple (zero |> succ |> succ |> succ) (zero |> succ |> succ));; (* renvoie "(3,2)\n" *)
empty |> decale_add |> prnt_lcpl;; (* renvoie "(0,1)\n" *)
empty |> decale_add |> decale_add |> prnt_lcpl;; (* renvoie "(1,2)\n" *)

(* Test de prédécesseur *)
pred three |> prnt_lint;; (* 2 *)
pred two |> prnt_lint;;
pred one |> prnt_lint;;
pred zero |> prnt_lint;;
int_to_lint 100 |> pred |> prnt_lint;;       


(*
  ----- ADDITION, SOUSTRACTION, MULTIPLICATION -----
*)

let add a b = iter a b succ;;
let subs a b = iter b a pred;;
let mul a b = iter b zero (fun x -> add a x);;

(* C'est très drole de constater la taille des types :

   val add :
  (((('a -> 'b) -> 'c -> 'a) -> ('a -> 'b) -> 'c -> 'b) -> 'd -> 'e) ->
  'd -> 'e = <fun>
   
val subs :
  'a ->
  (((((('b -> 'c -> 'c) -> ('d -> 'e) -> 'f -> 'd) ->
      ((('d -> 'e) -> 'f -> 'd) -> (('d -> 'e) -> 'f -> 'e) -> 'g) -> 'g) ->
     ((('h -> 'i -> 'i) -> ('j -> 'k -> 'k) -> 'l) -> 'l) ->
     ('m -> 'n -> 'm) -> 'o) ->
    'o) ->
   'a -> 'p) ->
  'p = <fun>
   
val mul :
  (((('a -> 'b) -> 'c -> 'a) -> ('a -> 'b) -> 'c -> 'b) -> 'd -> 'e) ->
  (('d -> 'e) -> ('f -> 'g -> 'g) -> 'h) -> 'h = <fun>

Il est à noté que de part la correspondance de Curry-Howard, créé ces fonctions correspond aussi à une
preuve mathématique de leurs équivalent propositionnel (nous somme simplement typé):
   pour add, on a la créé une preuve que ((A => B) => C => A) => ... => E
En effet, la réduction est la règle de "destruction" (TODO: re-vérifier) de l'implication
   tandis que la liaison + retour est la règle d'inférence
*)

(* Assez de baratin, l'heure du test ! *)
add three two |> lint_to_int;; (* 5 *)
subs (succ three) one |> lint_to_int;;
mul (mul three two) (mul (add three two) two) |> lint_to_int;; (* (2*3)*((3+2)*2) = 60 *)


(*
  ----- MACHINE DE CYTHAN (TIPE) -----
*)                                             

let phi a n = ifzerothen n ((a n) |> succ |> succ) (a n);; (* Ajoute 2 au premier élément *)

(*
  TODO: psi, puis les composés, et l'on aura une machine de Cythan sans interface !
*)
