rm -rf _site/*
lake exe presentation
cd _site
firefox localhost:8800 &
python3 -m http.server 8800
