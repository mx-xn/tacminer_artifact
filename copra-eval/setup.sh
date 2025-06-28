#!/bin/bash
# This is a stripped down version of the original Copra setup.sh script that 
# only sets up Coq, skipping Lean and Isabelle.
# Run it from the Copra root.

if [[ ! -d "src/scripts" ]]; then
    # Raise an error if the scripts directory is not present
    echo "Please run this script from the root of the repository, cannot find src/scripts"
    exit 1
fi
# Don't run without activating conda
# Check if Conda is activated
conda_status=$(conda info | grep "active environment" | cut -d ':' -f 2 | tr -d '[:space:]')
if [[ $conda_status == "None" ]] || [[ $conda_status == "base" ]]; then
    echo "Please activate conda environment before running this script"
    exit 1
fi
echo "Setting up Copra ..."
echo "[NOTE] The installation needs manual intervention on some steps. Please choose the appropriate option when prompted."
conda install pip
conda_bin=$(conda info | grep "active env location" | cut -d ':' -f 2 | tr -d '[:space:]')
pip_exe="$conda_bin/bin/pip"
ls -l $pip_exe
echo "Installing dependencies..."
# # For Lean:
# # https://leanprover-community.github.io/install/debian_details.html

echo "Installing OCaml (opam)..."
opam init -a --compiler=4.07.1
eval `opam config env`
opam update
# # For Coq:
echo "Installing Coq..."
opam pin add coq 8.10.2
opam pin -y add menhir 20190626
# # For SerAPI:
echo "Installing SerAPI (for interacting with Coq from Python)..."
opam install -y coq-serapi
echo "Installing Dpdgraph (for generating dependency graphs)..."
opam repo add coq-released https://coq.inria.fr/opam/released
opam install -y coq-dpdgraph
# Python dependencies
echo "Installing Python dependencies..."
$pip_exe install --user -r requirements.txt
echo "Clone all git submodules..."
git submodule update --init --recursive
echo "Cloned all git submodules successfully!"
echo "Building Coq projects..."
(
    # Build CompCert
    echo "Building CompCert..."
    echo "This may take a while... (don't underestimate the time taken to build CompCert, meanwhile you can take a coffee break!)"
    pushd ./data/benchmarks
    set -euv
    cd CompCert
    if [[ ! -f "Makefile.config" ]]; then
        ./configure x86_64-linux
    fi
    make -j `nproc`
    popd
    echo "CompCert built successfully!"
    # Ignore some proofs in CompCert
    # ./src/scripts/patch_compcert.sh
) || exit 1
echo "Building Coq's Simple Benchmark..."
pushd ./data/test/coq/custom_group_theory
cd theories
make
cd ..
popd
echo "Building Coq's Simple Benchmark done!"
echo "Copra's Coq Setup complete!"
