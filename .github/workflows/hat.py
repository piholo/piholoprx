name: Update hat
on:
  schedule:
    - cron: "10 10 * * *"
  workflow_dispatch:
permissions:
  contents: write  # To push changes to repository
  actions: write   # To manage workflows
  pull-requests: write  # If your workflow creates 
jobs:
  update-files:
    runs-on: ubuntu-latest
    concurrency:
      group: ${{ github.workflow }}-${{ github.ref }}
      cancel-in-progress: false
    
    steps:
      - name: Checkout repository
        uses: actions/checkout@v3
        with:
          fetch-depth: 0
          # Using the built-in GITHUB_TOKEN instead of a custom PAT
          token: ${{ secrets.GITHUB_TOKEN }}

      - name: Set up Python
        uses: actions/setup-python@v4
        with:
          python-version: '3.x'

      - name: Install dependencies
        run: |
          python -m pip install requests pytz
          python -m pip install --upgrade pip
          pip install python-dotenv
          pip install chardet

      - name: Pulisci file JSON esistenti
        run: |
          rm -f daddyliveSchedule.json
          echo "File JSON eliminati per garantire dati freschi"
          
      - name: Run script hat
        run: |
          python hat.py

      - name: Commit and push changes
        run: |
          git config --global user.name "github-actions[bot]"
          git config --global user.email "41898282+github-actions[bot]@users.noreply.github.com"
          
          # Ignore Python bytecode files to avoid binary conflicts
          echo "__pycache__/" >> .gitignore
          echo "*.pyc" >> .gitignore
          
          # Stage all changes
          git add .
          
          # Check if there are changes to commit
          if [[ -n $(git status --porcelain) ]]; then
            # Commit changes
            git commit -m "Update Itaevents $(date +%H:%M)"
            
            # Push changes using the built-in token
            git push
          else
            echo "No changes to commit"
          fi
