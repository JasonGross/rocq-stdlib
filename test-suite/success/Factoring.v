From Stdlib Require Import ZArith NArith List Factoring.
Import ListNotations.
Local Open Scope positive_scope.

Goal ppfactor 24 = [(2, 3); (3, 1)]. Proof. vm_compute. reflexivity. Qed.
Goal ppfactor 1 = []. Proof. vm_compute. reflexivity. Qed.
Goal ppfactor 1311 = [(3, 1); (19, 1); (23, 1)]. Proof. vm_compute. reflexivity. Qed.
Goal ppfactor (2^16+1) = [(65537, 1)]. Proof. vm_compute. reflexivity. Qed.
Goal factor 360 = [2; 2; 2; 3; 3; 5]. Proof. vm_compute. reflexivity. Qed.
Goal val 2 24 = 3%N. Proof. vm_compute. reflexivity. Qed.
Goal val 5 24 = 0%N. Proof. vm_compute. reflexivity. Qed.
Goal totient 20 = 8. Proof. vm_compute. reflexivity. Qed.
Goal totient 97 = 96. Proof. vm_compute. reflexivity. Qed.
