1. Install Nix: `sh <(curl -L https://nixos.org/nix/install) --daemon`
2. Add some nix-channels:

```
$ nix-channel --add https://nixos.org/channels/nixpkgs-21.11-darwin stable
$ nix-channel --add https://nixos.org/channels/nixpkgs-unstable unstable
$ nix-channel --update
$ nix-channel --list
stable https://nixos.org/channels/nixpkgs-21.11-darwin
unstable https://nixos.org/channels/nixpkgs-unstable
```

Then in a new terminal;

```
$ nix-env -iA stable.neovim
```

If this successfully installs neovim-0.5.1, then you know it worked.

3. Add the following to your `.config/nix/nix.conf`
```
system = aarch64-darwin
extra-platforms = aarch64-darwin x86_64
experimental-features = nix-command flakes

max-jobs = auto  # Allow building multiple derivations in parallel
keep-outputs = true  # Do not garbage-collect build time-only dependencies (e.g. clang)
# Allow fetching build results from the Lean Cachix cache
trusted-substituters = https://lean4.cachix.org/
trusted-public-keys = cache.nixos.org-1:6NCHdD59X431o0gWypbMrAURkbJ16ZPMQFGspcDShjY= lean4.cachix.org-1:mawtxSxcaiWE24xCXXgh3qnvlTkyU7evRRnGeAhD4Wk=
```

4. `nix-env -iA nixpkgs.direnv`, then add `eval "$(direnv hook zsh)"` to your .zshrc, and open a new terminal.

5. Clone Radiya: `git clone git@github.com:yatima-inc/Radiya.lean.git` and cd
   into it.

6. `$ direnv allow`, which should automatically build everything
7. `$ nix run .#test`
```
$ nix run .#test
UnsignedVarint:
✓ unsigned-varint
Multibase:
✓ basic
✓ case insensitivity
✓ leading zero
✓ two leading zeros
✓ RFC 4648
Multihash:
✓ sha3-512
DagCbor:
✓ DagCbor
```

8. This has been tested as of 01/28/22, but if for some reason the above doesn't
   work, updating the flake might help:

```
$ nix flake update
$ git add flake.lock
$ nix build
```
