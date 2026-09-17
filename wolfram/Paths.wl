(* Shared repository paths for scripts and direct Get calls. *)
$SUSYWBEProjectRoot = With[{override = Environment["BAE_BERTINI_ROOT"]},
  If[StringQ[override] && StringTrim[override] =!= "",
    ExpandFileName[override],
    DirectoryName[DirectoryName[$InputFileName]]
  ]
];
SUSYWBEProjectDirectory[] := $SUSYWBEProjectRoot;
SUSYWBEPackageDirectory[] := $SUSYWBEProjectRoot;
