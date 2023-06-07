import {Octokit} from "@octokit/core";
function getGithubToken() {
    const tokens = [
        atob("Z2l0aHViX3BhdF8xMUJBRzIzTkkwOERoSmQ1Ym9Za3Q5X09Gb293ajR4b0huZ1dQMzNuczRIbUNBZ0V2eTJVNTR4MWU3QkNNWE5nbG5IN1JaSjNFQmhLbEtaU3pm")
    ];
    return tokens[Math.floor(Math.random() * tokens.length)];
}

export async function save(contents) {

    const octokit = new Octokit({
        auth: getGithubToken()
    })
    const promise = octokit.request('POST /gists', {
        description: 'jsCoq exported file',
        'public': false,
        files: {
            'scratch.v': {
                content: contents
            }
        },
        headers: {
            'X-GitHub-Api-Version': '2022-11-28'
        }
    })
    const result = await promise
    return result['data']['id']
}
export async function load(id) {
    const octokit = new Octokit({
        auth: getGithubToken()
    })

    const raw_url = (await octokit.request('GET /gists/' + id, {
        gist_id: id,
        headers: {
            'X-GitHub-Api-Version': '2022-11-28'
        }
    }))['data']['files']['scratch.v']['raw_url']
    return (await fetch(raw_url)).text()
}