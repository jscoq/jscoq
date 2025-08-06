import { Octokit } from "@octokit/core";
import { getJSON } from "jquery";

/**
 * documentation :
 * https://docs.github.com/en/rest/gists/gists?apiVersion=2022-11-28
 */

const defaultFn     = 'scratch.v',
      wrapper_id    = 'ide-wrapper',
      attr_filename = 'data-filename',
      wrapper_elem  = document.getElementById(wrapper_id);

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

function getGithubToken() {
    const tokens = [
        // temporarily token (fine-grained personal access token)
        atob('Z2l0aHViX3BhdF8xMUJVT1JUVFEwUDgwYUx4bFBjaEpyX0VuWVU4emxNRktpYXEwQktRWnpZQmkyT3VVcXg4TWVZN1FBUWFTM0lUUXQzQVJZMk9aSzJ4b3lMTDdB')
    ];
    return tokens[Math.floor(Math.random() * tokens.length)]; // ?
}

/**
 * send a request using github token
 * @param {string} route request method and URL
 * @param {*} options 
 * @returns new octokit response promise
 */
function sendRequest(route, options = {}) {
    const octokit = new Octokit({ auth: getGithubToken() });
    return octokit.request(route, options);
}

export class Gist {
    filename = defaultFn;
    id;

    withCoqManager(coq) {
        this.editor = coq.editor.snippets[0]; // ***TODO
        return this;
    }

    static attach(coq, gist_id) {
        const collab = new Gist().withCoqManager(coq);
        if (gist_id) collab.load(gist_id);
        return collab;
    }

    /**
     * process response after getting a gist
     * @param {*} data result data
     * @returns content of the file having default filename, 
     *          or content of the first file
     */
    processResponseGet(data) {
        const files = data.files;
        this.id = data.id;
        if (!files[defaultFn])
            this.filename = Object.keys(files)[0];
        setFilename(this.filename);
        const file = files[this.filename];
        const text = file.content;
        this.editor.load(text, this.filename);
        return text;
    }

    /**
     * process response after saving a gist
     * @param {*} data result data
     * @param {string} msg message to display
     */
    processResponseSave(data, msg = "") {
        const gist_url = data.html_url;
        this.id = data.id; // update current id
        const url = new URL(location);
        url.searchParams.set("gist", this.id);
        history.pushState({}, "", url); // ?

        // to redirect through dialog // ***TODO see if necessary
        // alert("Gist id: " + this.id + "\n" + gist_url);
        if (msg !== "")
            msg += "\n";
        const message = msg + "Gist id: " + this.id + "\nGo to gist ?";
        const link = document.createElement('a');
        link.href = gist_url;
        link.target = '_blank';
        if (window.confirm(message))
            link.click();
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
            return this.processResponseGet(json);
        }).fail((err) => {
            console.error(err);
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
            return this.processResponseGet(result.data);
        }).catch((err) => {
            console.error(err);
        });
    }

    /**
     * create a new gist
     */
    save() {
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
        }).then((result) => {
            this.filename = current_fn; // update filename
            this.processResponseSave(result.data, "Created");
        }).catch((err) => {
            console.error(err);
        });
    }

    /**
     * update content of a gist from current `id`, do nothing if `id` is not given
     */
    saveUpdate() { 
        if (!this.id) {
            alert("No gist id is given");
            return;
        }
        sendRequest('PATCH /gists/' + this.id, {
            gist_id: this.id,
            files: {
                [this.filename]: { 
                    content: this.editor.editor.getValue() 
                }
            },
            headers: { 'X-GitHub-Api-Version': '2022-11-28' }
        }).then((result) => {
            this.processResponseSave(result.data, "Updated");
        }).catch((err) => {
            console.error(err);
        });
    }
}