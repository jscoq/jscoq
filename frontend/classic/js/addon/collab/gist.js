import { Octokit } from "@octokit/core";
import { RequestError } from "@octokit/request-error";
import { getJSON } from "jquery";

/**
 * documentation :
 * https://docs.github.com/en/rest/gists/gists?apiVersion=2022-11-28
 */

const default_fn    = 'scratch.v',
      wrapper_id    = 'ide-wrapper',
      attr_filename = 'data-filename',
      wrapper_elem  = document.getElementById(wrapper_id),
      ask_token_msg = "GitHub token with \"Gists\" user permissions (write) is required to continue.",
      notif_id      = "gist-notif";
let   notif_elem    = document.getElementById(notif_id);

if (!notif_elem) {
    notif_elem = document.createElement("div");
    notif_elem.setAttribute('id', notif_id);
    document.body.insertBefore(notif_elem, wrapper_elem);
}

function notification(elem) {
    notif_elem.replaceChildren(elem);
}

/**
 * set filename to html
 * @param {string} filename 
 */
function setFilename(filename) {
    wrapper_elem.setAttribute(attr_filename, filename);
}

/**
 * get filename from html
 * @returns filename
 */
function getFilename() {
    return wrapper_elem.getAttribute(attr_filename);
}

function getGithubToken() { // ***TODO
    const tokens = [
        // temporarily token (fine-grained personal access token)
        ""
    ];
    return tokens[Math.floor(Math.random() * tokens.length)];
}

function makeErrorMessage(err) {
    let status = err.status;
    let message;
    if (err.responseJSON) {
        message = err.responseJSON.message;
    } else if (err.response && err.response.data) {
        message = err.response.data.message
    } else {
        message = "";
    }
    message = "Error " + status + " " + message;
    let p = document.createElement('p');
    p.textContent = message;
    return p;
}

/**
 * send a request using github token
 * @param {string} route   request method and URL
 * @param {*}      options request options
 * @param {string} token   octokit authentication token
 * @returns new octokit response promise
 */
function sendRequest(route, options = {}, token = getGithubToken()) {
    const octokit = new Octokit({ auth: token });
    return octokit.request(route, options);
}

export class Gist {
    filename = default_fn;
    id;
    token;

    withCoqManager(coq) {
        this.editor = coq.editor.snippets[0]; // ***TODO
        return this;
    }

    static attach(coq, gist_id) {
        const collab = new Gist().withCoqManager(coq);
        if (gist_id) collab.loadNoAuth(gist_id);
        return collab;
    }

    /**
     * process response after loading a gist
     * @param {*} data result data
     * @returns content of the file having default filename, 
     *          or content of the first file
     */
    processResponseLoad(data) {
        const files = data.files;
        this.id = data.id;
        if (!files[default_fn])
            this.filename = Object.keys(files)[0];
        // if not any files
        if (!this.filename) return "";
        setFilename(this.filename);
        const file = files[this.filename];
        const text = file.content;
        this.editor.load(text, this.filename);
        return text;
    }

    /**
     * process response after saving a gist
     * @param {*}      data result data
     * @param {string} msg  message to display
     */
    processResponseSave(data, msg = "") {
        const gist_url = data.html_url;
        this.id = data.id; // update current id
        const url = new URL(location);
        url.searchParams.set("gist", this.id);
        history.pushState({}, "", url);

        // to redirect through notification (div msg) on top
        if (msg !== "")
            msg += "\n";
        const message = msg + "Gist id: ";
        const p = document.createElement("p");
        const link = document.createElement('a');
        link.href = gist_url;
        link.target = '_blank';
        link.innerText = this.id;
        p.textContent = message;
        p.appendChild(link);
        notification(p);
    }

    /**
     * get a gist by `id` without authentication
     * @param {string} id a gist id
     * @returns content of the gist obtained by id
     */
    loadNoAuth(id) {
        getJSON("https://api.github.com/gists/" + id, { 
            format: 'json' 
        }).done((json) => {
            return this.processResponseLoad(json);
        }).fail((err) => {
            console.error(err);
            notification(makeErrorMessage(err));
        });
    }

    /**
     * get a gist by `id`
     * @param {string} id a gist id
     * @returns content of the gist obtained by id
     */
    load(id) {
        sendRequest('GET /gists/' + id, {
            gist_id: id,
            headers: { 'X-GitHub-Api-Version': '2022-11-28' }
        }).then((result) => {
            return this.processResponseLoad(result.data);
        }).catch((err) => {
            console.error(err);
            notification(makeErrorMessage(err));
        });
    }

    /**
     * create a new gist
     */
    save() {
        let token;
        if (!this.token) {
            token = window.prompt(ask_token_msg);
            if (token === null) return;
            token = token.trim();
        }
        const current_fn = getFilename();
        sendRequest('POST /gists', {
            description: 'jsCoq exported file',
            'public': false,
            files: {
                [current_fn]: { 
                    content: this.editor.editor.getValue() 
                }
            },
            headers: { 'X-GitHub-Api-Version': '2022-11-28' }
        }, token)
        .then((result) => {
            if (!this.token) this.token = token;
            this.filename = current_fn; // update filename
            this.processResponseSave(result.data, "Created");
        }).catch((err) => {
            console.error(err);
            notification(makeErrorMessage(err));
        });
    }

    /**
     * update content of a gist from current `id`, do nothing if `id` is not given
     */
    saveUpdate() { 
        if (!this.id) {
            notification("No gist id is given");
            return;
        }
        let token;
        if (!this.token) {
            token = window.prompt(ask_token_msg);
            if (token === null) return;
            token = token.trim();
        }
        sendRequest('PATCH /gists/' + this.id, {
            gist_id: this.id,
            files: {
                [this.filename]: { 
                    content: this.editor.editor.getValue() 
                }
            },
            headers: { 'X-GitHub-Api-Version': '2022-11-28' }
        }, token).then((result) => {
            if (!this.token) this.token = token;
            this.processResponseSave(result.data, "Updated");
        }).catch((err) => {
            console.error(err);
            notification(makeErrorMessage(err));
        });
    }
}