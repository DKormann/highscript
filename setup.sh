
if lake build; then

echo "
to use HighScript as a global LEAN library add this to your .zshrc :

  export LEAN_PATH=\"$(pwd)/.lake/build/lib/lean\"
"
else
  exit 1
fi

