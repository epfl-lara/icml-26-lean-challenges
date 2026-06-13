import Challenges.Splay_Tree.Challenge_Splay_TraversalConjecture

open Lean Elab Command

elab "#print_splay_consts" : command => do
  let env ← getEnv
  for (n, ci) in env.constants.toList do
    if n.toString.startsWith "Splay." then
      logInfo m!"{n} : {ci.type}"

#print_splay_consts
