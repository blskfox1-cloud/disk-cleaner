@echo off
rem Запуск Disk Cleaner без консольного окна
chcp 65001 >nul
cd /d "%~dp0"
start "" pythonw "%~dp0disk_cleaner.py"
if errorlevel 1 (
  echo Не удалось запустить pythonw. Пробую python...
  python "%~dp0disk_cleaner.py"
  pause
)
