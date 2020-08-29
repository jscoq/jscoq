const { app, BrowserWindow, ipcMain, shell } = require('electron')

let win

function createWindow () {
  win = new BrowserWindow({
    width: 800,
    height: 600,
    webPreferences: {
      nodeIntegration: true
    }
  });

  win.loadFile('index.html');
  //win.openDevTools();

  win.on('closed', () => { win = null });
}

app.on('ready', createWindow)
app.on('window-all-closed', () => { app.quit() });

