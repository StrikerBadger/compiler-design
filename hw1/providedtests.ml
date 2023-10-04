open Assert
open Hellocaml

(* These tests are provided by you -- they will NOT be graded *)

(* You should also add additional test cases here to help you   *)
(* debug your program.                                          *)

let provided_tests : suite = [
  Test ("Student-Provided Tests For Problem 1-3", [
    ("case1", assert_eqf (fun () -> prob3_ans) 42);
    ("case2", assert_eqf (fun () -> (prob3_case2 17)) 25);
    ("case3", assert_eqf (fun () -> prob3_case3) 64);
  ]);
    (* CUSTOM *)
    Test("Friend Problem 4-5", [
      ("Friend optimize4", assert_eqf (fun () -> optimize (Add(Mult(Const 0L, Var "x"), Const 3L))) (Const 3L));
      ("Friend optimize5", assert_eqf (fun () -> optimize (Add(Mult(Const 0L, Var "x"), Mult(Const 0L, Var "x")))) (Const 0L));
      ("Friend optimize6", assert_eqf (fun () -> optimize (Mult((Const 0L), (Add (Var "x", Var "y"))))) (Const 0L));
      ("Friend optimize7", assert_eqf (fun () -> optimize (Mult((Const 1L), (Add (Var "x", Var "y"))))) (Add (Var "x", Var "y")));
      ("Friend optimize8", assert_eqf (fun () -> optimize (Add((Const 0L), (Add (Var "x", Var "y"))))) (Add (Var "x", Var "y")));
      ("Friend optimize9", assert_eqf (fun () -> optimize (Add (Var "x", Var "y"))) (Add (Var "x", Var "y")));
      ("Friend optimize10", assert_eqf (fun () -> optimize (Mult (Var "x", Var "y"))) (Mult (Var "x", Var "y")));
    ]);
  
    (* CUSTOM *)
    Test ("Friend Problem5", [
      ("Friend compile1", assert_eqf (fun() -> compile e1) [IPushC 6L]);
      ("Friend compile2", assert_eqf (fun() -> compile (Add(Const 2L, Const 3L))) ([IPushC 5L]));
      ("Friend compile3", assert_eqf (fun() -> compile e2) ([IPushV "x"; IPushC 1L; IAdd]));
      ("Friend compile3", assert_eqf (fun() -> compile e3) ([IPushV "y"; IPushV "x"; IPushC 1L; IAdd; IPushV "x"; IPushC 1L; IAdd; INeg; IMul; IMul]));
    ]);
      (* CUSTOM *)
  Test("Friend Problem 4-4", [  
    ("Friend interpret4", assert_eqf (fun () -> interpret ctxt2 e3) (-63L));
    ("Friend interpret5", assert_eqf (fun () -> interpret ctxt2 (Add(Mult(Var "x", Neg (Var "y")), Add(Neg e3, Neg e3)))) 112L);

    (* TODO more examples*)
  ]);

  Test
      ( "Student-Provided Tests For Problem 5",
        [
          ( "case1",
            assert_eq
              (optimize (Add (Var "a", Var "b")))
              (Add (Var "a", Var "b")) );
          ( "case2",
            assert_eq (optimize (Neg (Add (Const 1L, Const 1L)))) (Const (-2L))
          );
          ( "case3",
            assert_eq
              (optimize (Add (Mult (Const 0L, Var "b"), Const 0L)))
              (Const 0L) );
          ( "case4",
            assert_eq
              (optimize (Add (Mult (Const 1L, Var "b"), Const 0L)))
              (Var "b") );
        ] );
] 

