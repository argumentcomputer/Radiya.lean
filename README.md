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

- Install the [Nix package manager](https://nixos.org/download.html): `sh <(curl -L https://nixos.org/nix/install)
--daemon`
- Install [direnv](https://direnv.net/): `nix-env -iA nixpkgs.direnv`
- Hook direnv into your shell, by following these shell specific instructions: https://direnv.net/docs/hook.html. For example, in `zsh`, run `eval "$(direnv hook zsh)"`, or add that line to the end of your `~/.zshrc`
- Install [nixFlakes](https://nixos.wiki/wiki/Flakes): `nix-env -iA nixpkgs.nixUnstable`
- Enable nix flakes and commands.
  - If you already have a `nix.conf`, add `experimental-features = nix-command flakes` to `~/.config/nix/nix.conf`.
  - If you don't have a `nix.conf`: `mkdir -p ~/.config/nix && echo "experimental-features = nix-command flakes" > ~/.config/nix/nix.conf`.
- Clone this repo: `git clone https://github.com/yatima-inc/Radiya.lean.git`
- `cd` into that directory: `cd ~/Radiya.lean` if that's where you cloned it.
- Enable direnv: `direnv allow`
- Build Radiya: `nix build` (This might take a while the first time you run it)

For building on M1 MacOS, please see further information [here](/Build_on_M1_MacOS.md).
