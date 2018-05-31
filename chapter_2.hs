module Chapter_2
( Prop (P),
 pname,
 parse_propvar,
 parse_prop_formula,
 print_propvar,
 mk_and,
 mk_or,
 mk_imp,
 mk_iff,
 mk_forall,
 mk_exists,
 dest_iff,
 dest_and,
 conjuncts,
 dest_or,
 disjuncts,
 dest_imp,
 antecedent,
 consequent,
 onatoms,
 atom_union,
 atoms,
 eval,
 onallvaluations,
 print_truthtable,
 tautology,
 unsatisfiable,
 satisfiable,
 psubst,
 dual,
) where
import Parsing_FOL
import Data.List
import Data.Maybe

-- Chapter 2.1 The Syntax of propositional logic --

-- Primitive propositions --

data Prop = P String deriving (Show, Eq)

pname :: Prop -> String
pname (P s) = s

parse_propvar :: [[Char]] -> (Formula Prop, [[Char]])
parse_propvar (p:oinp) | p /= "(" = (Atom(P p), oinp)
parse_propvar _ = error "parse_propvar"

parse_prop_formula :: [Char] -> Formula Prop
parse_prop_formula = make_parser (parse_formula parse_propvar)

print_propvar :: Prop -> String
print_propvar (P s) = show s


-- Syntax operations --

mk_and :: Formula a -> Formula a -> Formula a
mk_and = And
mk_or = Or
mk_imp = Imp
mk_iff = Iff
mk_forall = Forall
mk_exists = Exists

dest_iff :: Formula a -> (Formula a, Formula a)
dest_iff (Iff p q) = (p, q)
dest_iff _ = error "dest_iff"

dest_and :: Formula a -> (Formula a, Formula a)
dest_and (And p q) = (p, q)
dest_and _ = error "dest_and"

conjuncts :: Formula a -> [Formula a]
conjuncts (And p q) = conjuncts p ++ conjuncts q
conjuncts fm = [fm]

dest_or :: Formula a -> (Formula a, Formula a)
dest_or (Or p q) = (p, q)
dest_or _ = error "dest_or"

disjuncts :: Formula a -> [Formula a]
disjuncts (Or p q) = disjuncts p ++ disjuncts q
disjuncts fm = [fm]

dest_imp :: Formula a -> (Formula a, Formula a)
dest_imp (Imp p q) = (p, q)
dest_imp _ = error "dest_imp"

antecedent :: Formula a -> Formula a
antecedent = fst.dest_imp

consequent :: Formula a -> Formula a
consequent = snd.dest_imp

onatoms :: (a -> Formula a) -> Formula a -> Formula a
onatoms f fm = case fm of
        (Atom a) -> f a
        (Not p) -> (Not (onatoms f p))
        (And p q) -> And (onatoms f p) (onatoms f q)
        (Or p q) -> Or (onatoms f p) (onatoms f q)
        (Imp p q) -> Imp (onatoms f p) (onatoms f q)
        (Iff p q) -> Iff (onatoms f p) (onatoms f q)
        (Forall x p) -> Forall x (onatoms f p)
        (Exists x p) -> Exists x (onatoms f p)
        _ -> fm

overatoms :: (a -> b -> b) -> Formula a -> b -> b
overatoms f fm b = case fm of
        (Atom a) -> f a b
        (Not p) -> overatoms f p b
        (And p q) -> overatoms f p (overatoms f q b)
        (Or p q) -> overatoms f p (overatoms f q b)
        (Imp p q) -> overatoms f p (overatoms f q b)
        (Iff p q) -> overatoms f p (overatoms f q b)
        (Forall x p) -> overatoms f p b
        (Exists x p) -> overatoms f p b
        _ -> b

atom_union :: Eq b => (a -> [b]) -> Formula a -> [b]
atom_union f fm = nub $ overatoms (\h t -> (f h) ++ t) fm []

-- Chapter 2.2 The semantics of propositional loogic --

atoms :: Eq a => Formula a -> [a]
atoms fm = atom_union (\a -> [a]) fm

eval :: Formula t -> (t -> Bool) -> Bool
eval fm v = case fm of
        Bottom -> False
        Top -> True
        (Atom a) -> v a
        (Not p) -> not (eval p v)
        (And p q) -> (eval p v) && (eval q v)
        (Or p q) -> (eval p v) || (eval p v)
        (Imp p q) -> not (eval p v) || (eval q v)
        (Iff p q) -> (eval p v) == (eval q v)

onallvaluations :: Eq a => ((a -> Bool) -> Bool) -> (a -> Bool) -> [a] -> Bool
onallvaluations subfn v ats = case ats of
        [] -> subfn v
        (p:ps) -> onallvaluations subfn (v' False) ps &&
                  onallvaluations subfn (v' True) ps
                        where v' t q | p == q = t
                                     | otherwise = v q

-- Truth-tables mechanized --

print_truthtable :: Formula Prop -> IO ()
print_truthtable fm =
    let ats = atoms fm in
    let width = 6 + ((length . pname . (maximumBy (\(P s) (P t) -> compare (length s) (length t)))) ats) in
    let fixw s = s ++ (take (width - (length s)) (repeat ' ')) in
    let truthstring p = fixw (if p then "true" else "false") in
    let mk_row v =  let lis = map (\ x -> truthstring (v x)) ats
                        ans = truthstring (eval fm v)
                    in putStrLn ((unwords lis) ++ "| " ++ ans) in
    let separator = take (width * (length ats) + 9) (repeat '-') in
    let printer v ats1 = case ats1 of
            [] -> mk_row v
            (p:ps) ->   let v' t q = if q == p then t else v q 
                        in (printer (v' False) ps) >> (printer (v' True) ps)
    in do   putStrLn ((concatMap (\ (P s) -> fixw s) ats) ++ "| formula")
            putStrLn separator
            printer (\ x -> False) ats

-- 2.3 Validity, satisfiability and tautology --

tautology :: Eq a => Formula a -> Bool
tautology fm = onallvaluations (eval fm) (\s -> False) (atoms fm)

unsatisfiable :: Eq a => Formula a -> Bool
unsatisfiable = tautology . Not

satisfiable ::Eq a => Formula a -> Bool 
satisfiable = not . unsatisfiable

psubst :: (a -> Formula a) -> Formula a -> Formula a
psubst = onatoms

-- psubst :: (a -> Maybe (Formula a)) -> Formula a -> Formula a
-- psubst subfn = onatoms (\x -> fromMaybe (Atom x) $ (subfn x))

-- psubst subfn = onatoms (\x -> case subfn x of
--                                      Just p -> p
--                                      Nothing -> Atom x

dual fm = case fm of
    Bottom -> Top
    Top -> Bottom
    Atom p -> fm
    Not p -> Not (dual p)
    And p q -> Or (dual p) (dual q)
    Or p q -> And (dual p) (dual q)
    _ -> error "Formula involves connectives ==> or <=>"
