(*Formues logiques et BDD*)

type tformula =
  |Value of bool
  |Var of string
  |Not of tformula
  |And of tformula * tformula
  |Or of tformula * tformula
  |Implies of tformula * tformula
  |Equivalent of tformula * tformula

type decTree =
  |DecLeaf of bool
  |DecRoot of string * decTree * decTree

let a1 = Var "A1"
let a2 = Var "A2"
let b1 = Var "B1"
let b2 = Var "B2"
let f1 = Equivalent(a1,Not(a2))
let f2 = Equivalent(Not(b1),b2)
let f_test = Or(f1,f2)


(*Question 1*)

let rec getVarsSorted f =
  match f with
  |Value v -> []
  |Var v -> [v]
  |Not(v1) -> List.sort compare (getVarsSorted v1)
  |And(v1,v2) -> List.sort compare (getVarsSorted v1 @ getVarsSorted v2)
  |Or(v1,v2) -> List.sort compare (getVarsSorted v1 @ getVarsSorted v2)
  |Implies(v1,v2) -> List.sort compare (getVarsSorted v1 @ getVarsSorted v2)
  |Equivalent(v1,v2) -> List.sort compare (getVarsSorted v1 @ getVarsSorted v2)
;;

let rec isIn a l =
  match l with
  |[]->false
  |h::l1 -> if (a = h) then true else isIn a l1
;;

let rec supprimeDoublon l =
  match l with
  |[]->[]
  |h::q -> if (isIn h q) then supprimeDoublon q else h::supprimeDoublon q 
;;

let getVars f =
  let l = getVarsSorted f in
  supprimeDoublon l
;;

(*TEST*)
assert(getVars f_test = ["A1";"A2";"B1";"B2"]);;

(*Question 2*)
type env =(string * bool) list

exception Variable_non_definie;;

(*Renvois la valeur de la variable définie dans l'environnement. On suppose que la variable est définie dans l'environnement.*)
let rec valOfVariable var ev =
  match ev with
  |[]->raise Variable_non_definie
  |h::q->match h with
         |(a,b)->if (a=var) then b else valOfVariable var q;
;;

(*On suppose que toutes les variables présentent dans f ont une valeur définie dans env*)
let rec evalFormula env f =
  match f with
  |Value v -> v
  |Var v -> valOfVariable v env
  |Not(v) -> if (evalFormula env v = true) then false else true
  |And(v1,v2) -> (match (evalFormula env v1,evalFormula env v2) with
                 |(true,true) -> true
                 |(true,false) -> false
                 |(false,true) -> false
                 |(false,false) -> false)
  |Or(v1,v2) ->(match (evalFormula env v1,evalFormula env v2) with
                |(true,true) -> true
                |(true,false) -> true
                |(false,true) -> true
                |(false,false) -> false)
  |Implies(v1,v2)->(match (evalFormula env v1,evalFormula env v2) with
                    |(true,true) -> true
                    |(true,false) -> false
                    |(false,true) -> true
                    |(false,false) -> true)
  |Equivalent(v1,v2)->(match (evalFormula env v1,evalFormula env v2) with
                       |(true,true) -> true
                       |(true,false) -> false
                       |(false,true) -> false
                       |(false,false) -> true)
;;

(*TEST*)
let env = ["A1",true;"A2",false;"B1",true;"B2",false];;
assert(evalFormula env f_test = true);;

let env = ["A1",false;"A2",false;"B1",false;"B2",false];;
assert(evalFormula env f_test = false);;

(*Question 3*)

let rec buildDecTree_aux f env (lv:string list)=
  match lv with
  |[]->DecLeaf(evalFormula env f)
  |h::q->DecRoot(h,(buildDecTree_aux f ((h,false)::env) q) ,(buildDecTree_aux f ((h,true)::env) q))
;;

let buildDecTree f =
  let lv = getVars f in
  let env = [] in
  buildDecTree_aux f env lv
;;

(*TEST*)
let dec = DecRoot ("A1",
 DecRoot ("A2",
  DecRoot ("B1", DecRoot ("B2", DecLeaf false, DecLeaf true),
   DecRoot ("B2", DecLeaf true, DecLeaf false)),
  DecRoot ("B1", DecRoot ("B2", DecLeaf true, DecLeaf true),
   DecRoot ("B2", DecLeaf true, DecLeaf true))),
 DecRoot ("A2",
  DecRoot ("B1", DecRoot ("B2", DecLeaf true, DecLeaf true),
   DecRoot ("B2", DecLeaf true, DecLeaf true)),
  DecRoot ("B1", DecRoot ("B2", DecLeaf false, DecLeaf true),
   DecRoot ("B2", DecLeaf true, DecLeaf false))))
;;

assert(buildDecTree f_test = dec);;

(*Question 4*)

type bddNode=
  |BddLeaf of int*bool
  |BddNode of int*string*int*int

type bdd =(int*(bddNode list))

let rec isInNode (b:bddNode) (node:bddNode list)=
  match node with
  |[]->false
  |h::q->if (h=b) then true else isInNode b q
;;


let getNextNumber l =
  match l with
  |[]->1
  |h::q->match h with 
         |BddLeaf(a,b)->a+1
         |BddNode(a,b,c,d) -> a+1
;;

(* let rec buildBddDec dec l=
  match dec with
  |DecLeaf(a) -> if
  |DecRoot(a,b,c) -> if (isInNode a l) then buildBddDec else 
;; 
 *)

(*Resultat attendu : *)
let bdd = (9,
 [BddNode (9, "A1", 7, 8); BddNode (8, "A2", 6, 4); BddNode (7, "A2", 4, 6);
  BddNode (6, "B1", 5, 5); BddNode (5, "B2", 1, 1); BddNode (4, "B1", 2, 3);
  BddNode (3, "B2", 1, 0); BddNode (2, "B2", 0, 1); BddLeaf (1, true);
  BddLeaf (0, false)]);;

(*Question 5*)

let rec listeDesNoeudsASimplifier lOfBddNode =
  match lOfBddNode with
  |[] -> []
  |h::q -> match h with
           |BddLeaf(a,b)->listeDesNoeudsASimplifier q
           |BddNode(a,b,c,d) -> if(c=d) then BddNode(a,b,c,d)::listeDesNoeudsASimplifier q else listeDesNoeudsASimplifier q
;;

let rec isLinkIn l node =
  match l with
  [] -> 0
  |h::q -> match h with 
           |BddLeaf(a,b) -> 0
           |BddNode(a,b,c,d) -> match node with
                                |BddLeaf(a,b) -> 0
                                |BddNode(x,y,z,t) -> if ((z=a) || (t=a)) then a else isLinkIn q node
;;

let rec extractNode n l =
  match l with
  |[]-> BddLeaf(0,false)
  |h::q -> match h with
           |BddLeaf(a,b) -> if (a=n) then BddLeaf(a,b) else extractNode n q
           |BddNode(a,b,c,d) -> if (a=n) then BddNode(a,b,c,d) else extractNode n q
;;


let rec simplifyLOfBdd lOfNode =
  let listeNode = (listeDesNoeudsASimplifier lOfNode) in
  match lOfNode with
  |[] -> []
  |h::q -> (match h with
            |BddLeaf(a,b) -> h::simplifyLOfBdd q
            |BddNode(a,b,c,d) -> if((isLinkIn listeNode h) != 0 ) then let e = extractNode (isLinkIn listeNode h) listeNode in (match e with
                                                                                                                               |BddNode(x,y,z,t) -> if(c=x) then simplifyLOfBdd ((BddNode(a,b,z,d))::q) else if (d=x) then simplifyLOfBdd ((BddNode(a,b,c,z))::q) else simplifyLOfBdd q;
                                                                                                                               |BddLeaf(x,y)->simplifyLOfBdd q) (*En théorie ce cas n'est jamais atteint car pour atteindre ce matching pattern, il faut que e soit un noeud à simplifier mais une feuille ne peut pas être simplifié dans une bdd*)
                                  else h::simplifyLOfBdd q
            )
;;

let rec clearSimplifiedNode l =
  match l with
  []->[]
  |h::q->match h with
         |BddLeaf(a,b) -> h::(clearSimplifiedNode q)
         |BddNode(a,b,c,d) -> if (c=d) then clearSimplifiedNode q else h::(clearSimplifiedNode q)
;;

let simplifyBdd bdd =
  match bdd with
  (a,l) -> (a,clearSimplifiedNode (simplifyLOfBdd l))
;;

(*TEST*)
let bddSimp=(9,
 [BddNode (9, "A1", 7, 8); BddNode (8, "A2", 1, 4); BddNode (7, "A2", 4, 1);
  BddNode (4, "B1", 2, 3);BddNode (3, "B2", 1, 0); BddNode (2, "B2", 0, 1); 
  BddLeaf (1, true);BddLeaf (0, false)]);;

assert(simplifyBdd bdd = bddSimp);;

(*Question 6*)

(*Prend en entrée une bdd, cette fonction existe pour essayer notre algo pour la fonction isTautology étant donné que nous n'avons pas réussi la question 4...*)
let isTautologyBdd bdd =
  let bddSimp = (simplifyBdd bdd) in
  match bddSimp with
  |(a,b) -> (match b with
            |h::q -> (match h with
                     |BddLeaf(a,b) -> if ((b=true) && (q=[])) then true else false
                     |_->false)
            |_->false)
;;

(* let isTautology f =
  let bdd = buildBdd f in
  isTautologyBdd
;; *)


(*TEST*)
assert(isTautologyBdd bdd = false)

let p = Var "P";;
let q = Var "Q";;
let h = Equivalent(p,q);;
let i = Implies(p,q);;
let j = Implies(q,p);;
let k = And(i,j);;
let l = Equivalent(h,k);;
let bddl=(2, [BddNode (2, "P", 1, 1); BddNode (1, "Q", 0, 0); BddLeaf (0, true)]);;

(*Question 7*)

let rec areEqualsList l1 l2 =
  match l1,l2 with
  |[],[]->true
  |h1::q1,h2::q2-> if (h1=h2) then areEqualsList q1 q2 else false
  |_,[]->false (*Cas où une des deux listes est vide alors elle ne sont pas égales*)
  |[],_->false
;; 

let areEqualsBdd bdd1 bdd2 =
  match bdd1,bdd2 with
  |(a1,b1),(a2,b2) -> if (a1=a2) then areEqualsList b1 b2 else false
;;

let areEquivalentBdd bdd1 bdd2 =
  let bdd1Simp = (simplifyBdd bdd1) in
  let bdd2Simp = (simplifyBdd bdd2) in
  areEqualsBdd bdd1Simp bdd2Simp
;;

(* let areEquivalent f1 f2 =
  let bdd1 = buildBdd f1 in
  let bdd2 = buildBdd f2 in
  areEquivalentBdd bdd1 bdd2
;; *)

(*TEST*)
assert(areEquivalentBdd bdd bddl = false);;


(*----Bonus----*)
(*Question 8*)

let string_of_bool (a:bool) =
  if (a = true) then "true" else "false"
;;

let rec dotDeclareNode fichier_sortie l =
  match l with
  |[]-> true
  |h::q->(match h with
         |BddLeaf(a,b) -> output_string fichier_sortie (String.concat "" [(string_of_int a);" [style = bold, label=\"";(string_of_bool b);"\"];\n"]); (dotDeclareNode fichier_sortie q);
         |BddNode(a,b,c,d) -> output_string fichier_sortie (String.concat "" [(string_of_int a);" [label =\"";b;"\"];\n"]); (dotDeclareNode fichier_sortie q);)
;;

let rec dotDeclareLink fichier_sortie l=
  match l with
  |[] -> true;
  |h::q->(match h with
          |BddLeaf(a,b) -> (dotDeclareLink fichier_sortie q);
          |BddNode(a,b,c,d) -> output_string fichier_sortie (String.concat "" [(string_of_int a);" -> ";(string_of_int c);" [color = red, style=dashed];\n";(string_of_int a);" -> ";(string_of_int d);";\n"]); (dotDeclareLink fichier_sortie q);)
;;

let extract_l_of_bdd bdd =
  match bdd with
  (a,l)->l
;;

let dotBDD nom_fichier bdd =
  let fichier_sortie = open_out nom_fichier; in
  let l = extract_l_of_bdd bdd in
  output_string fichier_sortie "digraph G{\n";
  dotDeclareNode fichier_sortie l;
  dotDeclareLink fichier_sortie l;
  output_string fichier_sortie "}";
  close_out fichier_sortie
;;

(*TEST*)
dotBDD "f_test.dot" bddSimp;;
(*Pour tracer l'arbre,executer la commande suivante dans un terminale : dot -Tpdf -o f_test.pdf f_test.dot*)

(*Question 9*)

let rec dotDec_aux dec i fichier =
  match dec with
  |DecLeaf(a) -> output_string fichier (String.concat "" [string_of_int i;" [style = bold, label=\"";(string_of_bool a);"\"];\n"]);
  |DecRoot(a,b,c) -> output_string fichier (String.concat "" [string_of_int i;" [label =\"";a;"\"];\n";(string_of_int i);" -> ";(string_of_int (2*i));" [color = red, style=dashed];\n";(string_of_int i);" -> ";(string_of_int ((2*i)+1));";\n"]); dotDec_aux b (2*i) fichier; dotDec_aux c ((2*i)+1) fichier;
;; 

let dotDec dec nom_fichier =
  let fichier = open_out nom_fichier; in
  output_string fichier "digraph G{\n";
  dotDec_aux dec 1 fichier;
  output_string fichier "}";
  close_out fichier
;;

(*TEST*)
dotDec dec "f_testDec.dot";;
(*Pour tracer l'arbre,executer la commande suivante dans un terminale : dot -Tpdf -o f_testDec.pdf f_testDec.dot*)

