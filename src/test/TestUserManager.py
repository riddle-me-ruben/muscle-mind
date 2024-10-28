import unittest
from unittest.mock import MagicMock
from flask import Flask, session
from src.server.UserManager import UserManager  

class TestUserManager(unittest.TestCase):

    def setUp(self):
        """Set up the Flask app and UserManager instance for testing."""
        self.app = Flask(__name__)
        self.app.secret_key = 'test_secret_key'  
        self.client = self.app.test_client()
        self.db_manager = MagicMock()  
        self.user_manager = UserManager(self.db_manager, session)

    def test_is_signed_in(self):
        """Test the is_signed_in method."""
        with self.app.test_request_context():
            session['email'] = 'test@example.com'
            self.assertTrue(self.user_manager.is_signed_in())

            session.pop('email', None)
            self.assertFalse(self.user_manager.is_signed_in())

    def test_user_exists(self):
        """Test the user_exists method."""
        email = 'existing_user@example.com'
        self.db_manager.execute_query.return_value = [{'email': email}]  
        result = self.user_manager.user_exists(email)
        self.assertIsNotNone(result)  

        self.db_manager.execute_query.return_value = None  
        result = self.user_manager.user_exists('non_existing_user@example.com')
        self.assertIsNone(result) 

    def test_add_user_success(self):
        """Test the add_user method for a new user."""
        with self.app.test_request_context():
            self.db_manager.execute_query.return_value = None  
            with self.client.session_transaction() as sess:
                sess['email'] = None 

            response = self.user_manager.add_user()
            self.assertIn("Registration successful!", response.data.decode('utf-8'))
            self.db_manager.execute_commit.assert_called_once_with(
                "INSERT INTO users (email, password) VALUES (%s, %s)", 
                ('test@example.com', 'password123')
            )

    def test_add_user_already_exists(self):
        """Test the add_user method when the email already exists."""
        with self.app.test_request_context():
            self.db_manager.execute_query.return_value = [{'email': 'test@example.com'}]  
            response = self.user_manager.add_user()
            self.assertIn("Email already exists.", response.data.decode('utf-8'))

    def test_login_success(self):
        """Test the login method for valid credentials."""
        with self.app.test_request_context():
            self.db_manager.execute_query.return_value = [{'email': 'test@example.com'}]
            with self.client.session_transaction() as sess:
                sess['email'] = None  

            response = self.user_manager.login()
            self.assertEqual(response.status_code, 302)  
            self.assertIn('email', session)  

    def test_login_failure(self):
        """Test the login method for invalid credentials."""
        with self.app.test_request_context():
            self.db_manager.execute_query.return_value = None

            response = self.user_manager.login()
            self.assertIn("Invalid email or password", response.data.decode('utf-8'))

    def test_logout(self):
        """Test the logout method."""
        with self.app.test_request_context():
            session['email'] = 'test@example.com'
            response = self.user_manager.logout()
            self.assertEqual(response.status_code, 302)
            self.assertNotIn('email', session) 

if __name__ == '__main__':
    unittest.main()
