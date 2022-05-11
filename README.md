# Radiya
A self-hosted Lean4 kernel with content-addressing

---
> Yatima grinned triumphantly, and recounted vis chain of reasoning. Radiya said
> calmly:
>
> "Good. You've just discovered the Gauss-Bonnet Theorem, linking the Euler
> number and total curvature." 
>
> "Really?" Yatima felt a surge of pride; Euler and Gauss were legendary
> miners - long-dead fleshers, but their skills had rarely been equaled.
>
> "Not quite." Radiya smiled slightly. "You should look up the precise statement
> of it, though; I think you're ready for a formal treatment of Riemannian
> spaces. But if it all starts to seem too abstract, don't be afraid to back off
> and play around with some more examples."
---

## Build

### Building with Lake

Run `lake build` in the root directory of this repo.

### Building with Nix

First, setup Nix

1. Install the [Nix package manager](https://nixos.org/download.html): `sh <(curl -L https://nixos.org/nix/install)
--daemon`
2. Install [direnv](https://direnv.net/): `nix-env -iA nixpkgs.direnv`
3. Hook direnv into your shell, by following these shell specific instructions: https://direnv.net/docs/hook.html. For example, in `zsh`, run `eval "$(direnv hook zsh)"`, or add that line to the end of your `~/.zshrc`
4. Install [nixFlakes](https://nixos.wiki/wiki/Flakes): `nix-env -iA nixpkgs.nixUnstable`
5. Enable nix flakes and commands.
  - If you already have a `nix.conf`, add `experimental-features = nix-command flakes` to `~/.config/nix/nix.conf`.
  - If you don't have a `nix.conf`: `mkdir -p ~/.config/nix && echo "experimental-features = nix-command flakes" > ~/.config/nix/nix.conf`

Now, in the root directory of this repo:

1. Enable direnv with `direnv allow`
2. Build Radiya with `nix build`

For building on M1 MacOS, please see further information [here](/Build_on_M1_MacOS.md).

## Develop

If you want to develop on Radiya, make sure you start your editor from a command
prompt in the root directory of the cloned repository so the Lean editor plugins
will trigger properly.

### Updating the Lean toolchain

When updating the `lean-toolchain` file to a more recent version, please make
sure to update the `flake.lock` file as well. This can be done with the command
`nix flake update`.

### Testing

This is done by a Lake script that runs each Lean file in [`test/in`](test/in)
and compares the output with the respective file in [`test/out`](test/out).

The script is capable of matching nested directories, such that for a given
`test/in/foo/bar.lean` it will look for a `test/out/foo/bar.out` to serve as the
reference for the expected output.

Run the tests with `lake script run tests`.
