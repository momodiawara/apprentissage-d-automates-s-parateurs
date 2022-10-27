(* Ce mini-projet porte sur l'apprentissage d'automates séparateurs.
   La lecture de la Section 15.3 des notes de cours est fortement
   recommandée. Le code que vous devez écrire prend en entrée deux
   listes de mots I et E, lues à partir d'un fichier passé en argument
   et renvoie sur la sortie standard le code SMT-LIB à faire passer
   dans une solveur SMT, comme Z3. 
 *)

open Printf

(* ensembles de test : ensemble I *)
let li = ["";"ab"]
             
(* ensembles de test : ensemble E *)
let le = ["aa";"b"]


(* ======================================================================= *)
(* EXERCICE 1 : extraire  l'alphabet de l'automate.
   La fonction alphabet_from_list prend en entrée une liste de
   chaînes de caractères et retourne une liste triée de
   caractères sans duplication. 
 *)
(* explode : string -> char list 
   prend une chaîne de caractères et renvoie la liste de ses caractères 
 *)
let explode s =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  exp (String.length s - 1) []

(* alphabet_from_list : string list -> char list  
   - prend en entrée une liste l de chaînes de caractères 
   - renvoie la liste triée et sans duplication de caractères
   apparaissant dans l
 *)
let rec insert x l = match l with
    []->[x]
   |a::b ->
     if (a>x) then x::l
     else if (a==x) then l
     else a::(insert x b);;
let rec sort l = match l with
    []->[]
  |[a]->[a]
  |a::b -> insert a(sort b);;
let rec appartient x l= match l with
    []-> false
   |a::b ->if(a=x) then true else appartient x b;;
(*tri sans doublon*)
let doubln l=
  let rec aux l' acc= match l' with
      []->List.rev acc
     |e::f ->
       if (appartient e f) then aux f acc
       else aux f (e::acc)
  in aux l [];;
(* transforme une liste de string en un seul string*)
let transform ls=
  let rec aux l s= match l with
      []->s
     |a::q -> aux q (s^a) in
  aux ls "";;

let  alphabet_from_list l =
  let rec aux l'= match l' with
      []->[]
     |[a]->[a]
     |a::b ->
       insert a (aux b)
  in aux (explode (transform l));;

  
(* test *)
 let a = alphabet_from_list (li @ le) ;;

(* ======================================================================= *)
(* EXERCICE 2 : définition de l'alphabet A et de l'arbre préfixe T en
   SMT-LIB Pour les listes données en exemple, la sortie de la
   fonction declare_types doit être la chaîne de caractères
   "(declare-datatypes () ((A a b) (T e ea eaa eab eb)))" *)

(* prefixes : string -> string list
   renvoie la liste des préfixes d'une chaîne de caractères 
   Nous allons ajouter à chaque préfixe le caractère 'e'.
   Par exemple, prefixes "aba" = ["e"; "ea"; "eab"; "eaba"] *)

let  prefixes s =
  let rec aux i l= 
    if i = (String.length s)+1 then l
    else aux (i+1) (l@["e" ^ String.sub s 0 (i)]) in
  aux 1 ["e"];;
  
(* prefixes_of_list : string list -> string list
   renvoie la liste triée et sans doublons des préfixes des chaînes 
   de caractères d'une liste donnée *)

(* transforme une liste de string en une list de tout les prefixes*)
let rec trans l' l= match l with
  []->l'
 |a::q -> trans (List.append l' (prefixes a)) q;;

let prefixes_of_list l =
  let rec aux l' l1= match l1 with
      []->l'
     |a::q -> aux (insert a l') q
  in aux [] (doubln(trans [] l));;

(* declare_types_alphabet : char list -> string
   - prend une liste de caractères [c_1; ...; c_n] et renvoie une chaîne 
   de la forme "(A c_1... c_n)" *)

let declare_types_alphabet cl =
  let rec aux l s= match l with
      []-> "(A" ^ s ^ ")\n" 
     |a::q -> aux q (s ^ " "^(String.make 1 a)) in
  aux cl "";;

(* declare_types_trie : string list -> string 
   - prend une liste l de chaînes de caractères et 
   renvoie une chaîne de la forme "(T es_1 ... es_n)" où 
   s_1... s_n est une énumération de tous les 
   prefixes des chaînes apparaissant dans l *)

  
let declare_types_trie l =
  let rec aux l' s= match l' with
      []-> "      (T" ^ s ^ ")" 
     |a::q -> aux q (s ^ " " ^   a) in
  aux (sort (prefixes_of_list l)) "";;

(* declare_types : string list -> char list -> string *)  
let declare_types l cl =
  "(declare-datatypes () "^
    (declare_types_alphabet cl)^
      (declare_types_trie l) ^")";;

(* test *)
(*Printf.printf "%s" (declare_types (li @ le) a) *)
  

(* ======================================================================= *)
(* EXERCICE 3 : définir une chaîne de caractères pour les définitions
   en SMT-LIB de
   - l'ensemble d'états Q,
   - la fonction delta de transition de l'automate,
   - l'ensemble final des états acceptants et
   - la fonction f,
   ainsi que les assertions associées.
   Ces définitions ne dépendent pas des listes de mots acceptés ou rejetés. *)

 let define_sorts_and_functions  =
   "(define-sort Q () Int)
    (declare-const n Q)
    (assert (> n 0))
    (declare-fun delta (Q A) Q)
    (assert (forall ((q Q) (a A))
    (and (>= (delta q a) 0) (< (delta q a) n))))
    (declare-fun final (Q) Bool)
    (declare-fun f (T) Q)
    (assert (forall ((x T))
    (and (>= (f x) 0) (< (f x) n))))
    (assert (= 0 (f e)))\n";;

(* ======================================================================= *)
(* EXERCICE 4 : contraintes sur les transitions
   La fonction assert_transition_constraints prend en entrée une trie 
   et retourne une chaîne qui modélise les contraintes sur les transitions 
   de l'automate décrites par la formule (51). *)
  
(* eq_trans_constr : string -> char -> string
   - renvoi une chaîne de caractères qui correspond à une formule atomique pour 
   la transition étiquetée avec 'a' à partir de l'état s
   Par exemple, pour s = "abc" et  c = 'd' on a 
   eq_trans_constr outputs "(= (f abcd)  (delta (f abc)  d))" *)
let eq_trans_constr s a =
 "(= (f " ^ s^Char.escaped a ^ ")  (delta (f " ^ s^" ) "^  Char.escaped a ^"))";; 

(* list_transition_constraints : string list -> string list
   prend une liste de chaînes de caractères et génère une liste 
   de formules atomiques ou de chaînes vides comme suit
   - pour une chaîne non vide de la forme sa on obtient
   une chaine correspondant à l'équation f(sa)= delta (fs) a
   - pour la chaîne vide on obtient la chaîne vide *)
let list_transition_constraints l =
  let rec aux l' li= match l' with
      []-> List.rev li
     |a::q ->
       if(a="" || String.length a <=1) then aux q ( ""::li)
       else
         aux q ((eq_trans_constr
                   (String.sub a 0 ((String.length a)-1))
                   (a.[(String.length a)-1]))::li)
  in aux l [];;
 
  
(* assert_transition_constraints : string list -> string
   - prend en entrée une liste de mots et renvoie une chaîne qui modélise 
   les contraintes sur les transitions de l'automate décrit par la 
   formule (51).
   Par example, pour la liste [""; "ab"; "aa"; "b"] on obtient la chaîne
   "(assert (and 
               (= (f ea)  (delta (f e)  a))
               (= (f eaa)  (delta (f ea)  a))
               (= (f eab)  (delta (f ea)  b))
               (= (f eb)  (delta (f e)  b))))"
 *)
let assert_transition_constraints l =
  let rec aux l1 s= match l1 with
      []-> "(assert (and" ^ s ^ "))\n"
     |a::q-> aux q ( s ^"\n"^ a )
  in aux (list_transition_constraints(
            prefixes_of_list l)) "";;
        
(* test *)
(*Printf.printf "%s" (assert_transition_constraints (li @ le))*)

(* ======================================================================= *)


(* EXERCICE 5 : contraintes sur les états acceptants La fonction
   assert_acceptance prend en entrée deux listes de mots et retourne
   une chaîne de caractères qui modélise les contraintes sur les états
   acceptants décrites par la formule (52). *)

(* eq_accept : string -> string 
   - prend une chaîne de caractères s et renvoie une chaîne de caractères 
   qui modélise l'appartenance de s à l'ensemble final des états acceptants *)
let eq_accept s =
  "(final (f e" ^ s ^"))";;

(* eq_non_accept : string -> string 
   - prend une chaîne de caractères s et renvoie une chaîne de caractères 
   qui modélise la non-appartenance de s à l'ensemble final des états acceptants 
 *)
let eq_non_accept s =
"(not(final (f e" ^ s ^")))";;

(* assert_acceptance : string list -> string list > string
   prend deux listes de chaînes de caractères, li et le, et renvoie une
   chaine qui modélise les contraintes sur les états acceptants
   décrites par la formule (52). 
   Les mots dans li sont acceptés et les mots dans le ne le sont pas. *)

let assert_acceptance li le  =
  let rec aux  s l = match l with
      []-> s ^ ")\n(check-sat-using (then qe smt))\n(get-model)\n(exit)\n"
     |a::q ->
       if(appartient a li)
       then aux (s ^"\n   "^ (eq_accept a)) q
       else aux ( s ^"\n   "^ ( eq_non_accept a)) q
  in aux "(assert (and  " (li@List.rev le);;

(* test *)
(*Printf.printf "%s" (assert_acceptance li le)*)
 
(* ======================================================================= *)
(* EXERCICE 6 :
   La fonction smt_code prend en entrée deux listes de mots
   et retourne une chaîne de caractères qui donne l'implémentation 
   en SMT-LIB. *)

(* smt_code : string list -> string list -> string 
   prend deux listes de chaînes de caractères, li et le, et renvoie une chaîne 
   de caractères qui donne l'implémentation en SMT-LIB.
   Les mots dans li sont acceptés et les mots dans le ne le sont pas. 
   Pour vérifier votre algorithme, vous pouvez essayer le code SMT-LIB 
   que vous obtenez dans le solveur Z3: https://rise4fun.com/z3 *)
let smt_code li le =
  Printf.printf "%s" (declare_types (li @ le) a);
  Printf.printf "\n%s" define_sorts_and_functions;
   assert_acceptance li le;;
  
(* test *)
(* Printf.printf "%s" (smt_code li le) *)
  

(* ======================================================================= *)
(* lire deux listes de chaîne de caractères I et E d'un fichier *)
(* Ne pas modifier cette partie *)

let input_line_opt ic =
  try Some (input_line ic)
  with End_of_file -> None
                    
let read_lines ic =
  let rec aux acc =
    match input_line_opt ic with
    | Some line -> aux (line::acc)
    | None -> (List.rev acc)
  in
  aux []
  
let lines_of_file filename =
  let ic = open_in filename in
  let lines = read_lines ic in
  close_in ic;
  (lines)

let read_lists_from_file (filename: string): ((string list) * (string list))  =
  let lines = lines_of_file filename in
  (String.split_on_char ' ' (List.nth lines 0),
   String.split_on_char ' ' (List.nth lines 1))
  
let () =
  let (li,le) = (read_lists_from_file Sys.argv.(1)) in
  Printf.printf "%s" (smt_code li le)

