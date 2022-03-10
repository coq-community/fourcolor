{
  ## DO NOT CHANGE THIS
  format = "1.0.0";
  ## unless you made an automated or manual update
  ## to another supported format.

  ## The attribute to build, either from nixpkgs
  ## of from the overlays located in `.nix/coq-overlays`
  attribute = "fourcolor";

  ## If you want to select a different attribute
  ## to serve as a basis for nix-shell edit this
  # shell-attribute = "{{nix_name}}";

  ## Maybe the shortname of the library is different from
  ## the name of the nixpkgs attribute, if so, set it here:
  # pname = "{{shortname}}";

  ## Lists the dependencies, phrased in terms of nix attributes.
  ## No need to list Coq, it is already included.
  ## These dependencies will systematically be added to the currently
  ## known dependencies, if any more than Coq.
  ## /!\ Remove this field as soon as the package is available on nixpkgs.
  ## /!\ Manual overlays in `.nix/coq-overlays` should be preferred then.
  # buildInputs = [ ];

  ## Indicate the relative location of your _CoqProject
  ## If not specified, it defaults to "_CoqProject"
  # coqproject = "_CoqProject";

  ## select an entry to build in the following `bundles` set
  ## defaults to "default"
  default-bundle = "8.15+1.14";

  ## write one `bundles.name` attribute set per
  ## alternative configuration, the can be used to
  ## compute several ci jobs as well
  bundles = let 
    mc13 = {
      mathcomp.override.version = "1.13.0";
      mathcomp.job = false;
    };
    mc14 = {
      mathcomp.override.version = "mathcomp-1.14.0";
      mathcomp.job = false;
    };             
  in {
    "8.12+1.13".coqPackages = { coq.override.version = "8.12"; } // mc13;
    "8.13+1.13".coqPackages = { coq.override.version = "8.13"; } // mc13;
    "8.14+1.13".coqPackages = { coq.override.version = "8.14"; } // mc13;
    "8.15+1.13".coqPackages = { coq.override.version = "8.14"; } // mc13;
    "8.12+1.14".coqPackages = { coq.override.version = "8.12"; } // mc14;
    "8.13+1.14".coqPackages = { coq.override.version = "8.13"; } // mc14;
    "8.14+1.14".coqPackages = { coq.override.version = "8.14"; } // mc14;
    "8.15+1.14".coqPackages = { coq.override.version = "8.15"; } // mc14;

  ## you may mark a package as a CI job as follows
  #  coqPackages.<another-pkg>.ci.job = "test";
  ## It can then be built throught
  ## nix-build --argstr ci "default" --arg ci-job "test";

  };

  ## Cachix caches to use in CI
  ## Below we list some standard ones
  cachix.coq = {};
  cachix.math-comp = {};
  cachix.coq-community.authToken = "CACHIX_AUTH_TOKEN";

  ## If you have write access to one of these caches you can
  ## provide the auth token or signing key through a secret
  ## variable on GitHub. Then, you should give the variable
  ## name here. For instance, coq-community projects can use
  ## the following line instead of the one above:
  # cachix.coq-community.authToken = "CACHIX_AUTH_TOKEN";

  ## Or if you have a signing key for a given Cachix cache:
  # cachix.my-cache.signingKey = "CACHIX_SIGNING_KEY"

  ## Note that here, CACHIX_AUTH_TOKEN and CACHIX_SIGNING_KEY
  ## are the names of secret variables. They are set in
  ## GitHub's web interface.
}
