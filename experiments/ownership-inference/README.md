Clone the git repo.

git clone https://github.com/hkim15/hafnium-verification.git

Build and install Infer.
When asked if you want to build clang, say yes.

cd hafnium-verification/experiments/ownership-inference/infer
./build-infer.sh clang

Add infer's bin directory in your path.

Build Hafnium.

cd ../infer
make PROJECT=reference

Check if infer works properly on Hafnium.

cd out/reference
infer --compilation-database compile_commands.json


